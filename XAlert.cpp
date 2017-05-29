
/*
 * XAlert.cpp
 * 
 * By Jiaqi Liu
 * E-mail: flyingeek@live.com
 * 
 */

#include <stdio.h>
#include <string.h>
#define _USE_MATH_DEFINES
#include <cmath>
#include <sstream>

#include "XPLMDisplay.h"
#include "XPLMGraphics.h"
#include "XPLMProcessing.h"
#include "XPLMDataAccess.h"
#include "XPLMMenus.h"
#include "XPLMUtilities.h"
#include "XPWidgets.h"
#include "XPStandardWidgets.h"
#include "XPLMPlugin.h"


#if APL
#include <Carbon/Carbon.h>
#endif

#ifdef _WIN32
#include <al.h>
#include <alc.h>
#else
#include <OpenAL/al.h>
#include <OpenAL/alc.h>
#endif

 /**************************************************************************************************************
 * WAVE FILE LOADING
 **************************************************************************************************************/

 // You can just use alutCreateBufferFromFile to load a wave file, but there seems to be a lot of problems with 
 // alut not beign available, being deprecated, etc.  So...here's a stupid routine to load a wave file.  I have
 // tested this only on x86 machines, so if you find a bug on PPC please let me know.

 // Macros to swap endian-values.

#define SWAP_32(value)                 \
        (((((unsigned short)value)<<8) & 0xFF00)   | \
         ((((unsigned short)value)>>8) & 0x00FF))

#define SWAP_16(value)                     \
        (((((unsigned int)value)<<24) & 0xFF000000)  | \
         ((((unsigned int)value)<< 8) & 0x00FF0000)  | \
         ((((unsigned int)value)>> 8) & 0x0000FF00)  | \
         ((((unsigned int)value)>>24) & 0x000000FF))

// Wave files are RIFF files, which are "chunky" - each section has an ID and a length.  This lets us skip
// things we can't understand to find the parts we want.  This header is common to all RIFF chunks.
struct chunk_header {
	int			id;
	int			size;
};

// WAVE file format info.  We pass this through to OpenAL so we can support mono/stereo, 8/16/bit, etc.
struct format_info {
	short		format;				// PCM = 1, not sure what other values are legal.
	short		num_channels;
	int			sample_rate;
	int			byte_rate;
	short		block_align;
	short		bits_per_sample;
};

// Airports meta data
struct airport_metadata
{
	int airportId;
	char name[256];
	char city[256];
	char country[256];
	char IATA[32];
	char ICAO[32];
	double latitude;
	double longitude;
	double altitude;
	double timezone;
	char DST[16];
	char tzDatabaseTimezone[256];
	char type[256];
	char source[256];
};

static airport_metadata airports[10000];
static int airports_cout;

#define FAIL(X) { XPLMDebugString(X); free(mem); return 0; }

#define RIFF_ID 0x46464952			// 'RIFF'
#define FMT_ID  0x20746D66			// 'FMT '
#define DATA_ID 0x61746164			// 'DATA'


#define earthRadiusKm 6371.0
#define KilometersToNauticalMilesRatio 0.539956804  // 1 KM = 0.539956804 NM
#define MAX_ITEMS 11

static XPLMDataRef gPositionDataRef[MAX_ITEMS];

static char DataRefString[MAX_ITEMS][255] = { "sim/flightmodel/position/local_x", "sim/flightmodel/position/local_y", "sim/flightmodel/position/local_z",
"sim/flightmodel/position/lat_ref", "sim/flightmodel/position/lon_ref",	"sim/flightmodel/position/theta",
"sim/flightmodel/position/phi", "sim/flightmodel/position/psi",
"sim/flightmodel/position/latitude", "sim/flightmodel/position/longitude", "sim/flightmodel/position/elevation" };

static char DataRefDesc[MAX_ITEMS][255] = { "Local x", "Local y", "Local z", "Lat Ref", "Lon Ref", "Theta", "Phi", "Psi" };
static char Description[3][255] = { "Latitude", "Longitude", "Elevation" };

static int	Element = 0, IntVals[128];
static float FloatVals[128];
static int ByteVals[128];

static int MenuItem1;

static long AlertDistance;
static double DestinationAirpotLat, DestinationAirpotlon;
static bool alertSet;

static XPWidgetID			ConfigWidget = NULL, ConfigWindow = NULL;
static XPWidgetID			CreateAlertButton = NULL;
static XPWidgetID			DistanceText = NULL;
static XPWidgetID			DistanceEdit = NULL;
static XPWidgetID			DistanceUpArrow = NULL;
static XPWidgetID			DistanceDownArrow = NULL;
static XPWidgetID			DestinationText = NULL;
static XPWidgetID			DestinationEdit = NULL;

static XPWidgetID			WarningText = NULL;

static XPWidgetID			ConfigApplyButton = NULL, LatLonRefApplyButton = NULL, ReloadSceneryButton = NULL;
static XPWidgetID			Position2Text[3] = { NULL };
static XPWidgetID			Position2Edit[3] = { NULL };

static void ConfigMenuHandler(void *, void *);

static void CreateConfigMenu(int x1, int y1, int w, int h);

static int ConfigHandler(
	XPWidgetMessage			inMessage,
	XPWidgetID				inWidget,
	intptr_t				inParam1,
	intptr_t				inParam2);

static bool setAlert(char *err);

static double distanceEarth(double lat1d, double lon1d, double lat2d, double lon2d);

static void buildFilePath(char *fileName, char *buf);

static bool launchVisualStudioDebugger();

static int getAirportIndexByICAO(char *ICAO);

static void cancelAlert();

static ALuint			snd_src = 0;				// Sample source and buffer - this is one "sound" we play.
static ALuint			snd_buffer = 0;
static float			pitch = 1.0f;			// Start with 1.0 pitch - no pitch shift.

static ALCdevice *		my_dev = NULL;			// We make our own device and context to play sound through.
static ALCcontext *		my_ctx = NULL;

// This is a stupid logging error function...useful for debugging, but not good error checking.
static void CHECK_ERR(void)
{
	ALuint e = alGetError();
	if (e != AL_NO_ERROR)
		printf("ERROR: %d\n", e);
}

// Mac specific: this converts file paths from HFS (which we get from the SDK) to Unix (which the OS wants).
// See this for more info:
//
// http://www.xsquawkbox.net/xpsdk/mediawiki/FilePathsAndMacho

#if APL
int ConvertPath(const char * inPath, char * outPath, int outPathMaxLen) {

	CFStringRef inStr = CFStringCreateWithCString(kCFAllocatorDefault, inPath, kCFStringEncodingMacRoman);
	if (inStr == NULL)
		return -1;
	CFURLRef url = CFURLCreateWithFileSystemPath(kCFAllocatorDefault, inStr, kCFURLHFSPathStyle, 0);
	CFStringRef outStr = CFURLCopyFileSystemPath(url, kCFURLPOSIXPathStyle);
	if (!CFStringGetCString(outStr, outPath, outPathMaxLen, kCFURLPOSIXPathStyle))
		return -1;
	CFRelease(outStr);
	CFRelease(url);
	CFRelease(inStr);
	return 0;
}
#endif

// This utility returns the start of data for a chunk given a range of bytes it might be within.  Pass 1 for
// swapped if the machine is not the same endian as the file.
static char *	find_chunk(char * file_begin, char * file_end, int desired_id, int swapped)
{
	while (file_begin < file_end)
	{
		chunk_header * h = (chunk_header *)file_begin;
		if (h->id == desired_id && !swapped)
			return file_begin + sizeof(chunk_header);
		if (h->id == SWAP_32(desired_id) && swapped)
			return file_begin + sizeof(chunk_header);
		int chunk_size = swapped ? SWAP_32(h->size) : h->size;
		char * next = file_begin + chunk_size + sizeof(chunk_header);
		if (next > file_end || next <= file_begin)
			return NULL;
		file_begin = next;
	}
	return NULL;
}

// Given a chunk, find its end by going back to the header.
static char * chunk_end(char * chunk_start, int swapped)
{
	chunk_header * h = (chunk_header *)(chunk_start - sizeof(chunk_header));
	return chunk_start + (swapped ? SWAP_32(h->size) : h->size);
}


inline	float	HACKFLOAT(float val)
{
	return val;
}

/*
#if IBM
inline	float	HACKFLOAT(float val)
{
return val;
}
#else
inline long long HACKFLOAT(float val)
{
double	d = val;
long long temp;
temp = *((long long *) &d);
return temp;
}
#endif
*/

static XPLMWindowID	gWindow = NULL;
static int				gClicked = 0;

static void MyDrawWindowCallback(
                                   XPLMWindowID         inWindowID,    
                                   void *               inRefcon);    

static void MyHandleKeyCallback(
                                   XPLMWindowID         inWindowID,    
                                   char                 inKey,    
                                   XPLMKeyFlags         inFlags,    
                                   char                 inVirtualKey,    
                                   void *               inRefcon,    
                                   int                  losingFocus);    

static int MyHandleMouseClickCallback(
                                   XPLMWindowID         inWindowID,    
                                   int                  x,    
                                   int                  y,    
                                   XPLMMouseStatus      inMouse,    
                                   void *               inRefcon);    

static ALuint load_wave(const char * file_name);

static void load_airports(const char * file_name);

static float init_sound(float elapsed, float elapsed_sim, int counter, void * ref);

/*
 * XPluginStart
 * 
 * Our start routine registers our window and does any other initialization we 
 * must do.
 * 
 */
PLUGIN_API int XPluginStart(
						char *		outName,
						char *		outSig,
						char *		outDesc)
{
	/* First we must fill in the passed in buffers to describe our
	 * plugin to the plugin-system. */

	//launchVisualStudioDebugger();

	strcpy(outName, "XAlert");
	strcpy(outSig, "jackil.xplugin.XAlert");
	strcpy(outDesc, "A plug-in that alert user on demand based on distance from current location to destination airport.");

	// init sound
	XPLMRegisterFlightLoopCallback(init_sound, -1.0, NULL);

	// init airports data
	char buf[2048];
	buildFilePath("airports.dat", buf);
	load_airports(buf);

	/* Now we create a window.  We pass in a rectangle in left, top,
	 * right, bottom screen coordinates.  We pass in three callbacks. */

	gWindow = XPLMCreateWindow(
					50, 90, 325, 50,	    /* Area of the window. */
					0,							/* Start visible. */
					MyDrawWindowCallback,		/* Callbacks */
					MyHandleKeyCallback,
					MyHandleMouseClickCallback,
					NULL);						/* Refcon - not used. */
					
	/* We must return 1 to indicate successful initialization, otherwise we
	 * will not be called back again. */

	XPLMMenuID	id;
	int			item;

	item = XPLMAppendMenuItem(XPLMFindPluginsMenu(), "XAlert", NULL, 1);

	id = XPLMCreateMenu("Config", XPLMFindPluginsMenu(), item, ConfigMenuHandler, NULL);
	XPLMAppendMenuItem(id, "Config", (void *)"Config", 1);

	MenuItem1 = 0;

	for (int Item = 0; Item<MAX_ITEMS; Item++)
		gPositionDataRef[Item] = XPLMFindDataRef(DataRefString[Item]);

	return 1;
}

/*
 * XPluginStop
 * 
 * Our cleanup routine deallocates our window.
 * 
 */
PLUGIN_API void	XPluginStop(void)
{
	XPLMDestroyWindow(gWindow);

	if (MenuItem1 == 1)
	{
		XPDestroyWidget(ConfigWidget, 1);
		MenuItem1 = 0;
	}

	// Cleanup: nuke our context if we have it.  This is hacky and bad - we should really destroy
	// our buffers and sources.  I have _no_ idea if OpenAL will leak memory.
	if (my_ctx) alcDestroyContext(my_ctx);
	if (my_dev) alcCloseDevice(my_dev);
	my_ctx = NULL;
	my_dev = NULL;
}

/*
 * XPluginDisable
 * 
 * We do not need to do anything when we are disabled, but we must provide the handler.
 * 
 */
PLUGIN_API void XPluginDisable(void)
{
}

/*
 * XPluginEnable.
 * 
 * We don't do any enable-specific initialization, but we must return 1 to indicate
 * that we may be enabled at this time.
 * 
 */
PLUGIN_API int XPluginEnable(void)
{
	return 1;
}

/*
 * XPluginReceiveMessage
 * 
 * We don't have to do anything in our receive message handler, but we must provide one.
 * 
 */
PLUGIN_API void XPluginReceiveMessage(
					XPLMPluginID	inFromWho,
					int				inMessage,
					void *			inParam)
{
}

/*
 * MyDrawingWindowCallback
 * 
 * This callback does the work of drawing our window once per sim cycle each time
 * it is needed.  It dynamically changes the text depending on the saved mouse
 * status.  Note that we don't have to tell X-Plane to redraw us when our text
 * changes; we are redrawn by the sim continuously.
 * 
 */
void MyDrawWindowCallback(
                                   XPLMWindowID         inWindowID,    
                                   void *               inRefcon)
{
	int		left, top, right, bottom;
	float	color[] = { 1.0, 1.0, 1.0 }; 	/* RGB White */
	
	/* First we get the location of the window passed in to us. */
	XPLMGetWindowGeometry(inWindowID, &left, &top, &right, &bottom);
	
	/* We now use an XPLMGraphics routine to draw a translucent dark
	 * rectangle that is our window's shape. */
	XPLMDrawTranslucentDarkBox(left, top, right, bottom);


	float FloatValue[MAX_ITEMS];
	double DoubleValue[3];

	char buffer[512];
	int Item;

	for (Item = 0; Item<MAX_ITEMS; Item++)
		FloatValue[Item] = XPLMGetDataf(gPositionDataRef[Item]);

	/// X, Y, Z, Lat, Lon, Alt
	XPLMLocalToWorld(FloatValue[0], FloatValue[1], FloatValue[2], &DoubleValue[0], &DoubleValue[1], &DoubleValue[2]);
	DoubleValue[2] *= 3.28;

	char lat[128], lon[128], elevation[128];

	snprintf(lat, sizeof(lat), "%lf", HACKFLOAT(DoubleValue[0]));
	snprintf(lon, sizeof(lon), "%lf", HACKFLOAT(DoubleValue[1]));
	snprintf(elevation, sizeof(elevation), "%lf", HACKFLOAT(DoubleValue[2]));

	char out1[200];

	if (alertSet)
	{
		double distanceToDestination = distanceEarth(atof(lat), atof(lon), DestinationAirpotLat, DestinationAirpotlon) * KilometersToNauticalMilesRatio;
		snprintf(out1, sizeof(out1), "Distance to destination airport:%.2lf nm", distanceToDestination);

		if (distanceToDestination < AlertDistance)
		{
			if (my_ctx)
			{

				ALCcontext * old_ctx = alcGetCurrentContext();
				alcMakeContextCurrent(my_ctx);

				alSourcef(snd_src, AL_PITCH, pitch);
				alSourcePlay(snd_src);

				CHECK_ERR();

				if (old_ctx)
					alcMakeContextCurrent(old_ctx);
			}

			cancelAlert();
		}
	}

	char out2[200];
	snprintf(out2, sizeof(out2), "Alert distance:%ld nm", AlertDistance);

	/* Finally we draw the text into the window, also using XPLMGraphics
	 * routines.  The NULL indicates no word wrapping. */
	XPLMDrawString(color, left + 10, top - 23, 
		(char*)(gClicked ? out2 : out1), NULL, xplmFont_Basic);
		
}                                   

/*
 * MyHandleKeyCallback
 * 
 * Our key handling callback does nothing in this plugin.  This is ok; 
 * we simply don't use keyboard input.
 * 
 */
void MyHandleKeyCallback(
                                   XPLMWindowID         inWindowID,    
                                   char                 inKey,    
                                   XPLMKeyFlags         inFlags,    
                                   char                 inVirtualKey,    
                                   void *               inRefcon,    
                                   int                  losingFocus)
{
}                                   

/*
 * MyHandleMouseClickCallback
 * 
 * Our mouse click callback toggles the status of our mouse variable 
 * as the mouse is clicked.  We then update our text on the next sim 
 * cycle.
 * 
 */
int MyHandleMouseClickCallback(
                                   XPLMWindowID         inWindowID,    
                                   int                  x,    
                                   int                  y,    
                                   XPLMMouseStatus      inMouse,    
                                   void *               inRefcon)
{
	/* If we get a down or up, toggle our status click.  We will
	 * never get a down without an up if we accept the down. */
	if ((inMouse == xplm_MouseDown) || (inMouse == xplm_MouseUp))
		gClicked = 1 - gClicked;
	
	/* Returning 1 tells X-Plane that we 'accepted' the click; otherwise
	 * it would be passed to the next window behind us.  If we accept
	 * the click we get mouse moved and mouse up callbacks, if we don't
	 * we do not get any more callbacks.  It is worth noting that we 
	 * will receive mouse moved and mouse up even if the mouse is dragged
	 * out of our window's box as long as the click started in our window's 
	 * box. */
	return 1;
}                                      

void ConfigMenuHandler(void * mRef, void * iRef)
{
	if (!strcmp((char *)iRef, "Config"))
	{if (MenuItem1 == 0)
		{
			CreateConfigMenu(300, 600, 300, 280);
			MenuItem1 = 1;
		}
		else
			if (!XPIsWidgetVisible(ConfigWidget))
				XPShowWidget(ConfigWidget);
	}
}

void CreateConfigMenu(int x, int y, int w, int h)
{
	int x2 = x + w;
	int y2 = y - h;
	float FloatValue[MAX_ITEMS];
	double DoubleValue[3];

	char buffer[512];

	for (int i = 0; i<MAX_ITEMS; i++)
		FloatValue[i] = XPLMGetDataf(gPositionDataRef[i]);

	/// X, Y, Z, Lat, Lon, Alt
	XPLMLocalToWorld(FloatValue[0], FloatValue[1], FloatValue[2], &DoubleValue[0], &DoubleValue[1], &DoubleValue[2]);
	DoubleValue[2] *= 3.28;

	ConfigWidget = XPCreateWidget(x, y, x2, y2,
		1,	// Visible
		"XAlert Config",	// desc
		1,		// root
		NULL,	// no container
		xpWidgetClass_MainWindow);

	XPSetWidgetProperty(ConfigWidget, xpProperty_MainWindowHasCloseBoxes, 1);

	ConfigWindow = XPCreateWidget(x + 20, y - 35, x2 - 20, y2 + 20,
		1,	// Visible
		"",	// desc
		0,		// root
		ConfigWidget,
		xpWidgetClass_SubWindow);

	XPSetWidgetProperty(ConfigWindow, xpProperty_SubWindowType, xpSubWindowStyle_SubWindow);

    int Item = 0;

	// Distance config item
	{
		DistanceText = XPCreateWidget(x + 30, y - (70 + (Item * 30)), x + 130, y - (92 + (Item * 30)),
			1,	// Visible
			"Alert Distance (nm)",// desc
			0,		// root
			ConfigWidget,
			xpWidgetClass_Caption);

		sprintf(buffer, "100");

		DistanceEdit = XPCreateWidget(x + 150, y - (70 + (Item * 30)), x + 240, y - (92 + (Item * 30)),
			1, buffer, 0, ConfigWidget,
			xpWidgetClass_TextField);

		XPSetWidgetProperty(DistanceEdit, xpProperty_TextFieldType, xpTextEntryField);

		DistanceUpArrow = XPCreateWidget(x + 250, y - (66 + (Item * 30)), x + 262, y - (81 + (Item * 30)),
			1, "", 0, ConfigWidget,
			xpWidgetClass_Button);

		XPSetWidgetProperty(DistanceUpArrow, xpProperty_ButtonType, xpLittleUpArrow);

		DistanceDownArrow = XPCreateWidget(x + 250, y - (81 + (Item * 30)), x + 262, y - (96 + (Item * 30)),
			1, "", 0, ConfigWidget,
			xpWidgetClass_Button);

		XPSetWidgetProperty(DistanceDownArrow, xpProperty_ButtonType, xpLittleDownArrow);
	}

	Item++;

	// Destination config item
	{
		DestinationText = XPCreateWidget(x + 30, y - (70 + (Item * 30)), x + 130, y - (92 + (Item * 30)),
			1,	// Visible
			"Destination ICAO",// desc
			0,		// root
			ConfigWidget,
			xpWidgetClass_Caption);

		sprintf(buffer, "KSEA");

		DestinationEdit = XPCreateWidget(x + 150, y - (70 + (Item * 30)), x + 240, y - (92 + (Item * 30)),
			1, buffer, 0, ConfigWidget,
			xpWidgetClass_TextField);

		XPSetWidgetProperty(DestinationEdit, xpProperty_TextFieldType, xpTextEntryField);
	}

	Item++;

	// Warning text
	{
		WarningText = XPCreateWidget(x + 50, y - (90 + (Item * 30)), x + 240, y - (112 + (Item * 30)),
			1,	// Visible
			"",// desc
			0,		// root
			ConfigWidget,
			xpWidgetClass_Caption);
	}


	ConfigApplyButton = XPCreateWidget(x + 70, y - 180, x + 220, y - 202,
		1, "Set alert", 0, ConfigWidget,
		xpWidgetClass_Button);

	// Version & info
	{
		XPCreateWidget(x + 50, y - 205, x + 240, y - 225,
			1,	// Visible
			"      XAlert alpha by Jiaqi Liu",// desc
			0,		// root
			ConfigWidget,
			xpWidgetClass_Caption);
		XPCreateWidget(x + 50, y - 225, x + 240, y - 250,
			1,	// Visible
			"    E-mail: flyingeek@live.com",// desc
			0,		// root
			ConfigWidget,
			xpWidgetClass_Caption);
	}

	XPSetWidgetProperty(ConfigApplyButton, xpProperty_ButtonType, xpPushButton);

	XPAddWidgetCallback(ConfigWidget, ConfigHandler);
}

void cancelAlert()
{
	alertSet = false;
	XPLMSetWindowIsVisible(gWindow, 0);
	XPSetWidgetDescriptor(WarningText, NULL);
	XPSetWidgetDescriptor(ConfigApplyButton, "Set alert");
}

int	ConfigHandler(
	XPWidgetMessage			inMessage,
	XPWidgetID				inWidget,
	intptr_t				inParam1,
	intptr_t				inParam2)
{
	char buffer[512];
	int Item;

	if (inMessage == xpMessage_CloseButtonPushed)
	{
		if (MenuItem1 == 1)
		{
			XPHideWidget(ConfigWidget);
		}
		return 1;
	}

	if (inMessage == xpMsg_PushButtonPressed)
	{
		if (inParam1 == (intptr_t)ConfigApplyButton)
		{
			if (alertSet)
			{
				cancelAlert();
				return 1;
			}

			char err[100];
			if (!setAlert(err))
			{
				XPSetWidgetDescriptor(WarningText, err);
			} else
			{
				XPLMSetWindowIsVisible(gWindow, 1);
				XPSetWidgetDescriptor(WarningText, "                Alert Set!");
				XPSetWidgetDescriptor(ConfigApplyButton, "Cancel alert");
			}

			return 1;
		}

		if (inParam1 == (intptr_t)DistanceUpArrow)
		{
			char buffer[128];
			XPGetWidgetDescriptor(DistanceEdit, buffer, 128);
			int distance = atoi(buffer) + 1;
			sprintf(buffer, "%d", distance);
			XPSetWidgetDescriptor(DistanceEdit, buffer);
			return 1;
		}

		if (inParam1 == (intptr_t)DistanceDownArrow)
		{
			char buffer[128];
			XPGetWidgetDescriptor(DistanceEdit, buffer, 128);
			int distance = atoi(buffer) - 1;
			sprintf(buffer, "%d", distance);
			XPSetWidgetDescriptor(DistanceEdit, buffer);
			return 1;
		}
		
	}
	return 0;
}

inline bool isInteger(const std::string & s)
{
	if (s.empty() || ((!isdigit(s[0])) && (s[0] != '-') && (s[0] != '+'))) return false;

	char * p;
	strtol(s.c_str(), &p, 10);

	return (*p == 0);
}

bool setAlert(char *err)
{
	char buffer[128];
	XPGetWidgetDescriptor(DistanceEdit, buffer, 128);

	if (!isInteger(buffer))
	{
		strcpy(err, "    Distance must be an integer");
		return false;
	}

	AlertDistance = atoi(buffer);

	if (AlertDistance <= 0)
	{
		strcpy(err, "    Distance should be positive");
		return false;
	}

	char ICAO[128];
	XPGetWidgetDescriptor(DestinationEdit, ICAO, 128);

	int index = getAirportIndexByICAO(ICAO);

	if (index == -1)
	{
		strcpy(err, "   Airport not found in database");
		return false;
	}

	DestinationAirpotLat = airports[index].latitude;
	DestinationAirpotlon = airports[index].longitude;

	alertSet = true;

	return true;
}


// This function converts decimal degrees to radians
double deg2rad(double deg) {
	return (deg * M_PI / 180);
}

//  This function converts radians to decimal degrees
double rad2deg(double rad) {
	return (rad * 180 / M_PI);
}

/**
* Returns the distance between two points on the Earth.
* Direct translation from http://en.wikipedia.org/wiki/Haversine_formula
* @param lat1d Latitude of the first point in degrees
* @param lon1d Longitude of the first point in degrees
* @param lat2d Latitude of the second point in degrees
* @param lon2d Longitude of the second point in degrees
* @return The distance between the two points in kilometers
*/
double distanceEarth(double lat1d, double lon1d, double lat2d, double lon2d) {
	double lat1r, lon1r, lat2r, lon2r, u, v;
	lat1r = deg2rad(lat1d);
	lon1r = deg2rad(lon1d);
	lat2r = deg2rad(lat2d);
	lon2r = deg2rad(lon2d);
	u = sin((lat2r - lat1r) / 2);
	v = sin((lon2r - lon1r) / 2);
	return 2.0 * earthRadiusKm * asin(sqrt(u * u + cos(lat1r) * cos(lat2r) * v * v));
}

void buildFilePath(char *fileName, char *buf)
{
	char dirchar = *XPLMGetDirectorySeparator();
	XPLMGetPluginInfo(XPLMGetMyID(), NULL, buf, NULL, NULL);
	char * p = buf;
	char * slash = p;
	while (*p)
	{
		if (*p == dirchar) slash = p;
		++p;
	}
	++slash;
	*slash = 0;
	strcat(buf, fileName);
#if APL
	ConvertPath(buf, buf, sizeof(buf));
#endif
}

char* replace_char(char* str, char find, char replace) {
	char *current_pos = strchr(str, find);
	while (current_pos) {
		*current_pos = replace;
		current_pos = strchr(current_pos, find);
	}
	return str;
}

// I put '$' symbol in the file to replace empty space so that I can easily parse it
// So I need to replace it back to fix it :)
void hacky_empty_fix(char *str)
{
	replace_char(str, '$', ' ');
}

void load_airports(const char * file_name)
{
	//open and get the file handle
	FILE* fp;
	fopen_s(&fp, file_name, "rb");

	//check if file exists
	if (fp == NULL) {
		printf("file does not exists %s", file_name);
		return;
	}

	int line_size = 2048;
	char line[2048];
	int index = 0;

	while (fgets(line, line_size, fp) != NULL) {

		sscanf(line, "%d%s%s%s%s%s%lf%lf%lf%lf%s%s%s%s",
			&airports[index].airportId, airports[index].name, airports[index].city, airports[index].country, 
			airports[index].IATA, airports[index].ICAO, &airports[index].latitude, &airports[index].longitude, &airports[index].altitude, 
			&airports[index].timezone, &airports[index].DST, airports[index].tzDatabaseTimezone, airports[index].type, airports[index].source);

		hacky_empty_fix(airports[index].name);
		hacky_empty_fix(airports[index].city);
		hacky_empty_fix(airports[index].country);
		hacky_empty_fix(airports[index].type);
		hacky_empty_fix(airports[index].source);

		index++;
	}

	airports_cout = index;

	fclose(fp);
}

int getAirportIndexByICAO(char *ICAO)
{
	char *p = ICAO;
	while (*p++ = toupper(*p));

	for (int i = 0; i < airports_cout; i++)
	{
		if (strcmp(ICAO, airports[i].ICAO) == 0) return i;
	}
	return -1;
}

ALuint load_wave(const char * file_name)
{
	// First: we open the file and copy it into a single large memory buffer for processing.

	FILE * fi = fopen(file_name, "rb");
	if (fi == NULL)
	{
		XPLMDebugString("WAVE file load failed - could not open.\n");
		return 0;
	}
	fseek(fi, 0, SEEK_END);
	int file_size = ftell(fi);
	fseek(fi, 0, SEEK_SET);
	char * mem = (char*)malloc(file_size);
	if (mem == NULL)
	{
		XPLMDebugString("WAVE file load failed - could not allocate memory.\n");
		fclose(fi);
		return 0;
	}
	if (fread(mem, 1, file_size, fi) != file_size)
	{
		XPLMDebugString("WAVE file load failed - could not read file.\n");
		free(mem);
		fclose(fi);
		return 0;
	}
	fclose(fi);
	char * mem_end = mem + file_size;

	// Second: find the RIFF chunk.  Note that by searching for RIFF both normal
	// and reversed, we can automatically determine the endian swap situation for
	// this file regardless of what machine we are on.

	int swapped = 0;
	char * riff = find_chunk(mem, mem_end, RIFF_ID, 0);
	if (riff == NULL)
	{
		riff = find_chunk(mem, mem_end, RIFF_ID, 1);
		if (riff)
			swapped = 1;
		else
			FAIL("Could not find RIFF chunk in wave file.\n")
	}

	// The wave chunk isn't really a chunk at all. :-(  It's just a "WAVE" tag 
	// followed by more chunks.  This strikes me as totally inconsistent, but
	// anyway, confirm the WAVE ID and move on.

	if (riff[0] != 'W' ||
		riff[1] != 'A' ||
		riff[2] != 'V' ||
		riff[3] != 'E')
		FAIL("Could not find WAVE signature in wave file.\n")

		char * format = find_chunk(riff + 4, chunk_end(riff, swapped), FMT_ID, swapped);
	if (format == NULL)
		FAIL("Could not find FMT  chunk in wave file.\n")

		// Find the format chunk, and swap the values if needed.  This gives us our real format.

		format_info * fmt = (format_info *)format;
	if (swapped)
	{
		fmt->format = SWAP_16(fmt->format);
		fmt->num_channels = SWAP_16(fmt->num_channels);
		fmt->sample_rate = SWAP_32(fmt->sample_rate);
		fmt->byte_rate = SWAP_32(fmt->byte_rate);
		fmt->block_align = SWAP_16(fmt->block_align);
		fmt->bits_per_sample = SWAP_16(fmt->bits_per_sample);
	}

	// Reject things we don't understand...expand this code to support weirder audio formats.

	if (fmt->format != 1) FAIL("Wave file is not PCM format data.\n")
		if (fmt->num_channels != 1 && fmt->num_channels != 2) FAIL("Must have mono or stereo sound.\n")
			if (fmt->bits_per_sample != 8 && fmt->bits_per_sample != 16) FAIL("Must have 8 or 16 bit sounds.\n")
				char * data = find_chunk(riff + 4, chunk_end(riff, swapped), DATA_ID, swapped);
	if (data == NULL)
		FAIL("I could not find the DATA chunk.\n")

		int sample_size = fmt->num_channels * fmt->bits_per_sample / 8;
	int data_bytes = chunk_end(data, swapped) - data;
	int data_samples = data_bytes / sample_size;

	// If the file is swapped and we have 16-bit audio, we need to endian-swap the audio too or we'll 
	// get something that sounds just astoundingly bad!

	if (fmt->bits_per_sample == 16 && swapped)
	{
		short * ptr = (short *)data;
		int words = data_samples * fmt->num_channels;
		while (words--)
		{
			*ptr = SWAP_16(*ptr);
			++ptr;
		}
	}

	// Finally, the OpenAL crud.  Build a new OpenAL buffer and send the data to OpenAL, passing in
	// OpenAL format enums based on the format chunk.

	ALuint buf_id = 0;
	alGenBuffers(1, &buf_id);
	if (buf_id == 0) FAIL("Could not generate buffer id.\n");

	alBufferData(buf_id, fmt->bits_per_sample == 16 ?
		(fmt->num_channels == 2 ? AL_FORMAT_STEREO16 : AL_FORMAT_MONO16) :
		(fmt->num_channels == 2 ? AL_FORMAT_STEREO8 : AL_FORMAT_MONO8),
		data, data_bytes, fmt->sample_rate);
	free(mem);
	return buf_id;
}

// Sound Initialization code.
static float init_sound(float elapsed, float elapsed_sim, int counter, void * ref)
{
	// We have to save the old context and restore it later, so that we don't interfere with X-Plane
	// and other plugins.

	ALCcontext * old_ctx = alcGetCurrentContext();

	// Try to create our own default device and context.  If we fail, we're dead, we won't play any sound.

	my_dev = alcOpenDevice(NULL);
	if (my_dev == NULL)
	{
		XPLMDebugString("Could not open the default OpenAL device.\n");
		return 0;
	}
	my_ctx = alcCreateContext(my_dev, NULL);
	if (my_ctx == NULL)
	{
		if (old_ctx)
			alcMakeContextCurrent(old_ctx);
		alcCloseDevice(my_dev);
		my_dev = NULL;
		XPLMDebugString("Could not create a context.\n");
		return 0;
	}

	// Make our context current, so that OpenAL commands affect our, um, stuff.

	alcMakeContextCurrent(my_ctx);

	ALfloat	zero[3] = { 0 };

	// Generate 1 source and load a buffer of audio.
	alGenSources(1, &snd_src);
	CHECK_ERR();
	// Build a path to "alert.wav" in our parent directory.	
	char buf[2048];
	buildFilePath("alert.wav", buf);
	snd_buffer = load_wave(buf);
	CHECK_ERR();

	// Basic initializtion code to play a sound: specify the buffer the source is playing, as well as some 
	// sound parameters. This doesn't play the sound - it's just one-time initialization.
	alSourcei(snd_src, AL_BUFFER, snd_buffer);
	alSourcef(snd_src, AL_PITCH, 1.0f);
	alSourcef(snd_src, AL_GAIN, 1.0f);
	alSourcei(snd_src, AL_LOOPING, 0);
	alSourcefv(snd_src, AL_POSITION, zero);
	alSourcefv(snd_src, AL_VELOCITY, zero);
	CHECK_ERR();

	// Finally: put back the old context _if_ we had one.  If old_ctx was null, X-Plane isn't using OpenAL.

	if (old_ctx)
		alcMakeContextCurrent(old_ctx);
	return 0.0f;
}

bool launchVisualStudioDebugger()
{
	// Get System directory, typically c:\windows\system32
	std::wstring systemDir(MAX_PATH + 1, '\0');
	UINT nChars = GetSystemDirectoryW(&systemDir[0], systemDir.length());
	if (nChars == 0) return false; // failed to get system directory
	systemDir.resize(nChars);

	// Get process ID and create the command line
	DWORD pid = GetCurrentProcessId();
	std::wostringstream s;
	s << systemDir << L"\\vsjitdebugger.exe -p " << pid;
	std::wstring cmdLine = s.str();

	// Start debugger process
	STARTUPINFOW si;
	ZeroMemory(&si, sizeof(si));
	si.cb = sizeof(si);

	PROCESS_INFORMATION pi;
	ZeroMemory(&pi, sizeof(pi));

	if (!CreateProcessW(NULL, &cmdLine[0], NULL, NULL, FALSE, 0, NULL, NULL, &si, &pi)) return false;

	// Close debugger process handles to eliminate resource leak
	CloseHandle(pi.hThread);
	CloseHandle(pi.hProcess);

	// Wait for the debugger to attach
	while (!IsDebuggerPresent()) Sleep(100);

	// Stop execution so the debugger can take over
	DebugBreak();
	return true;
}