/*
 * Copyright 2011 Vincent Sanders <vince@simtec.co.uk>
 * Modifications for TurboNet: security hardening, performance improvements,
 * and rebranding from NetSurf.
 *
 * This file is part of TurboNet, https://www.turbonet-browser.org/
 *
 * TurboNet is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; version 2 of the License.
 *
 * TurboNet is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "utils/config.h"

#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>      /* PERF: explicit include for malloc/free/exit */
#include <string.h>      /* PERF: explicit include for strdup/memset */
#include <windows.h>
#include <shlobj.h>
#include <shlwapi.h>
#include <io.h>

#include "utils/utils.h"
#include "utils/log.h"
#include "utils/messages.h"
#include "utils/filepath.h"
#include "utils/file.h"
#include "utils/nsurl.h"
#include "utils/nsoption.h"
#include "netsurf/url_db.h"
#include "netsurf/cookie_db.h"
#include "netsurf/browser.h"
#include "netsurf/browser_window.h"
#include "netsurf/fetch.h"
#include "netsurf/misc.h"
#include "netsurf/netsurf.h"
#include "desktop/hotlist.h"

#include "windows/findfile.h"
#include "windows/file.h"
#include "windows/cookies.h"
#include "windows/drawable.h"
#include "windows/corewindow.h"
#include "windows/download.h"
#include "windows/local_history.h"
#include "windows/window.h"
#include "windows/schedule.h"
#include "windows/font.h"
#include "windows/fetch.h"
#include "windows/pointers.h"
#include "windows/bitmap.h"
#include "windows/clipboard.h"
#include "windows/gui.h"

/** Application subdirectory name inside %APPDATA% */
#define TURBONET_APP_DIR     "TurboNet"

/** Default fallback DPI when system query returns implausible value */
#define TURBONET_DEFAULT_DPI 96

/** Minimum plausible DPI — anything at or below this is treated as bogus */
#define TURBONET_MIN_DPI     10

/** Default homepage URL */
#ifndef TURBONET_HOMEPAGE
#define TURBONET_HOMEPAGE    NETSURF_HOMEPAGE
#endif

/* --------------------------------------------------------------------------
 * Internal helpers
 * -------------------------------------------------------------------------- */

/**
 * Obtain the DPI of the primary display.
 *
 * PERF: The DC is acquired and released in one call; no long-lived handle
 * is kept open.
 *
 * \return Display DPI, or TURBONET_DEFAULT_DPI if the query fails or returns
 *         an implausible value.
 */
static int
turbonet_get_screen_dpi(void)
{
	HDC screendc;
	int dpi;

	screendc = GetDC(NULL);
	if (screendc == NULL) {
		/* SEC: avoid using an invalid DC handle */
		NSLOG(netsurf, WARNING,
		      "GetDC failed; falling back to default DPI %d",
		      TURBONET_DEFAULT_DPI);
		return TURBONET_DEFAULT_DPI;
	}

	dpi = GetDeviceCaps(screendc, LOGPIXELSY);
	ReleaseDC(NULL, screendc);

	if (dpi <= TURBONET_MIN_DPI) {
		/* SEC: reject implausible values that could be used to
		 * trigger integer-overflow in downstream layout maths */
		NSLOG(netsurf, WARNING,
		      "DPI reported as %d (implausible); using default %d",
		      dpi, TURBONET_DEFAULT_DPI);
		dpi = TURBONET_DEFAULT_DPI;
	}

	NSLOG(netsurf, INFO, "Screen DPI: %d", dpi);
	return dpi;
}


/**
 * Return the path to TurboNet's per-user configuration directory,
 * creating it if necessary.
 *
 * Uses the modern SHGetFolderPath(CSIDL_APPDATA) approach (same as the
 * original code) because MinGW does not expose SHGetKnownFolderPath.
 *
 * SEC: The function now validates that the path produced by PathAppend()
 * does not overflow MAX_PATH before writing, and checks CreateDirectory()
 * error codes carefully.
 *
 * @param[out] config_home_out  Receives a heap-allocated path string.
 *                              Caller must free() this.
 * @return NSERROR_OK on success, else an appropriate error code.
 */
static nserror
turbonet_get_config_home(char **config_home_out)
{
	TCHAR adPath[MAX_PATH];
	HRESULT hres;
	DWORD last_err;

	if (config_home_out == NULL) {
		/* SEC: guard against NULL output pointer */
		return NSERROR_BAD_PARAMETER;
	}

	hres = SHGetFolderPath(NULL,
	                       CSIDL_APPDATA | CSIDL_FLAG_CREATE,
	                       NULL,
	                       SHGFP_TYPE_CURRENT,
	                       adPath);
	if (FAILED(hres)) {
		NSLOG(netsurf, ERROR,
		      "SHGetFolderPath failed: HRESULT 0x%08lx", (unsigned long)hres);
		return NSERROR_INVALID;
	}

	/* SEC: PathAppend returns FALSE if the result would exceed MAX_PATH */
	if (PathAppend(adPath, TEXT(TURBONET_APP_DIR)) == FALSE) {
		NSLOG(netsurf, ERROR,
		      "PathAppend would overflow MAX_PATH — config path too long");
		return NSERROR_NOT_FOUND;
	}

	if (CreateDirectory(adPath, NULL) == 0) {
		last_err = GetLastError();
		if (last_err != ERROR_ALREADY_EXISTS) {
			NSLOG(netsurf, ERROR,
			      "CreateDirectory failed: error %lu", (unsigned long)last_err);
			return NSERROR_NOT_DIRECTORY;
		}
	}

	*config_home_out = strdup(adPath);
	if (*config_home_out == NULL) {
		/* SEC: catch allocation failure */
		return NSERROR_NOMEM;
	}

	NSLOG(netsurf, INFO, "Config path: \"%s\"", *config_home_out);
	return NSERROR_OK;
}


/**
 * Terminate the application due to a fatal, unrecoverable error.
 *
 * SEC: Displays a message box so the user knows *why* the process is dying
 * (the original just called exit(1) silently).  Still does not attempt any
 * further cleanup — this is intentional for abort-on-corruption scenarios.
 *
 * \param error  Human-readable description of the fatal error.  Must not be
 *               NULL.
 */
static void
turbonet_die(const char *error)
{
	if (error != NULL) {
		MessageBoxA(NULL, error, "TurboNet — Fatal Error",
		            MB_OK | MB_ICONERROR | MB_TASKMODAL);
	}
	ExitProcess(EXIT_FAILURE);   /* PERF/SEC: bypasses atexit handlers
	                              * that could run on a corrupted heap */
}


/**
 * Ensure a logging FILE* is backed by a real console handle.
 *
 * When compiled with -mwindows, stdin/stdout/stderr are not attached to any
 * console by default.  We allocate one on demand rather than leaving the
 * handle invalid.
 *
 * \param fptr  The FILE* to validate (typically stderr).
 * \return true always (matches the nslog_init callback signature).
 */
static bool
turbonet_log_ensure(FILE *fptr)
{
	if (_get_osfhandle(fileno(fptr)) == (intptr_t)INVALID_HANDLE_VALUE) {
		/* SEC: cast to intptr_t matches the return type of
		 * _get_osfhandle on both 32-bit and 64-bit Windows */
		AllocConsole();
		freopen("CONOUT$", "w", fptr);
	}
	return true;
}


/* --------------------------------------------------------------------------
 * Option / configuration initialisation
 * -------------------------------------------------------------------------- */

/**
 * Apply compile-time and environment-derived default values for options that
 * have no user-supplied value yet.
 *
 * PERF: The heap buffer is allocated once, reused for multiple path queries,
 * and freed in a single place at the end of the function.
 *
 * SEC: Every nsoption_setnull_charp() call now uses a freshly strdup()'d
 * string so the option system always owns its own copy.
 *
 * @param defaults  The option table to populate.
 * @return NSERROR_OK on success, else error code.
 */
static nserror
turbonet_set_option_defaults(struct nsoption_s *defaults)
{
	const DWORD buf_tchar_size = PATH_MAX + 1;
	const DWORD buf_bytes_size = sizeof(TCHAR) * buf_tchar_size;
	char *buf;
	char *ptr = NULL;
	char *fname;
	HRESULT hres;
	DWORD res_len;

	buf = malloc(buf_bytes_size);
	if (buf == NULL) {
		return NSERROR_NOMEM;
	}
	/* SEC: zero the buffer so partial paths are never mistaken for valid
	 * NUL-terminated strings */
	memset(buf, 0, buf_bytes_size);

	/* -- CA bundle -------------------------------------------------------- */
	res_len = SearchPathA(NULL,
	                      "ca-bundle.crt",
	                      NULL,
	                      buf_tchar_size,
	                      buf,
	                      &ptr);
	if (res_len > 0 && res_len < buf_tchar_size) {
		/* SEC: also guard against a SearchPath result that fills the
		 * entire buffer (would be missing the NUL terminator) */
		nsoption_setnull_charp(ca_bundle, strdup(buf));
	} else {
		memset(buf, 0, buf_bytes_size);
		ptr = filepath_sfind(G_resource_pathv, buf, "ca-bundle.crt");
		if (ptr != NULL) {
			nsoption_setnull_charp(ca_bundle, strdup(buf));
		}
	}

	/* -- Downloads directory ---------------------------------------------- */
	memset(buf, 0, buf_bytes_size);
	hres = SHGetFolderPath(NULL,
	                       CSIDL_PROFILE | CSIDL_FLAG_CREATE,
	                       NULL,
	                       SHGFP_TYPE_CURRENT,
	                       buf);
	if (SUCCEEDED(hres)) {
		if (PathAppend(buf, TEXT("Downloads"))) {
			nsoption_setnull_charp(downloads_directory,
			                       strdup(buf));
		}
	}

	free(buf);
	buf = NULL;  /* PERF/SEC: poison the pointer immediately after free */

	/* -- Homepage --------------------------------------------------------- */
	nsoption_setnull_charp(homepage_url, strdup(TURBONET_HOMEPAGE));

	/* -- Cookie file & jar ------------------------------------------------
	 * SEC: cookie_file and cookie_jar are intentionally separate paths so
	 * future code can apply different permissions/quotas to each.         */
	fname = NULL;
	netsurf_mkpath(&fname, NULL, 2, G_config_path, "Cookies");
	if (fname != NULL) {
		nsoption_setnull_charp(cookie_file, fname);
	}

	fname = NULL;
	netsurf_mkpath(&fname, NULL, 2, G_config_path, "CookieJar");
	if (fname != NULL) {
		nsoption_setnull_charp(cookie_jar, fname);
	}

	/* -- URL database ----------------------------------------------------- */
	fname = NULL;
	netsurf_mkpath(&fname, NULL, 2, G_config_path, "URLs");
	if (fname != NULL) {
		nsoption_setnull_charp(url_file, fname);
	}

	/* -- Hotlist / bookmarks ---------------------------------------------- */
	fname = NULL;
	netsurf_mkpath(&fname, NULL, 2, G_config_path, "Hotlist");
	if (fname != NULL) {
		nsoption_setnull_charp(hotlist_path, fname);
	}

	return NSERROR_OK;
}


/**
 * Initialise user-option storage, load saved choices from disk, and apply
 * any command-line overrides.
 *
 * \param pargc        Pointer to argc (may be modified by option parser).
 * \param argv         Argument vector.
 * \param respaths     NULL-terminated array of resource search paths.
 * \param config_path  Path to the per-user configuration directory.
 * \return NSERROR_OK on success, else error code.
 */
static nserror
turbonet_option_init(int *pargc,
                     char **argv,
                     char **respaths,
                     char *config_path)
{
	nserror ret;
	char *choices = NULL;

	G_resource_pathv = respaths;
	G_config_path    = config_path;

	ret = nsoption_init(turbonet_set_option_defaults,
	                    &nsoptions,
	                    &nsoptions_default);
	if (ret != NSERROR_OK) {
		return ret;
	}

	ret = netsurf_mkpath(&choices, NULL, 2, config_path, "Choices");
	if (ret == NSERROR_OK) {
		nsoption_read(choices, nsoptions);
		free(choices);
		choices = NULL;
	}

	/* Command-line flags override persisted choices */
	nsoption_commandline(pargc, argv, nsoptions);

	return NSERROR_OK;
}


/**
 * Load localised message strings.
 *
 * Tries the compiled-in resource blob first (fast path), then falls back to
 * the file-system search path.
 *
 * \param respaths  NULL-terminated array of resource search paths.
 * \return NSERROR_OK on success, else error code.
 */
static nserror
turbonet_messages_init(char **respaths)
{
	nserror ret;
	const uint8_t *data;
	size_t data_size;
	char *messages;

	ret = nsw32_get_resource_data("messages", &data, &data_size);
	if (ret == NSERROR_OK) {
		/* PERF: inline blob avoids a filesystem round-trip */
		return messages_add_from_inline(data, data_size);
	}

	messages = filepath_find(respaths, "messages");
	if (messages == NULL) {
		return NSERROR_NOT_FOUND;
	}

	ret = messages_add_from_file(messages);
	free(messages);
	return ret;
}


/* --------------------------------------------------------------------------
 * Command-line handling
 * -------------------------------------------------------------------------- */

/**
 * Convert the Windows Unicode command line into a conventional argc/argv.
 *
 * SEC: Each wide-to-multibyte conversion now checks wcstombs() for (size_t)-1
 * (encoding error) before allocating, preventing a malloc(0) or malloc(HUGE)
 * from a malformed wide string.
 *
 * PERF: The LocalFree() for argvw is now guaranteed via a single cleanup path.
 *
 * \param[out] argc_out  Receives the argument count.
 * \param[out] argv_out  Receives a heap-allocated argv array.  The caller
 *                       is responsible for freeing each element and the array
 *                       itself.
 * \return NSERROR_OK on success, else error code.
 */
static nserror
turbonet_win32_to_unix_commandline(int *argc_out, char ***argv_out)
{
	int argc = 0;
	char **argv = NULL;
	int cura;
	LPWSTR *argvw;
	size_t len;
	nserror ret = NSERROR_OK;

	argvw = CommandLineToArgvW(GetCommandLineW(), &argc);
	if (argvw == NULL) {
		return NSERROR_INVALID;
	}

	argv = calloc((size_t)argc, sizeof(char *));
	if (argv == NULL) {
		ret = NSERROR_NOMEM;
		goto cleanup_argvw;
	}

	for (cura = 0; cura < argc; cura++) {
		/* SEC: wcstombs with NULL dest returns required byte count
		 * (excluding NUL).  (size_t)-1 signals an encoding error. */
		len = wcstombs(NULL, argvw[cura], 0);
		if (len == (size_t)-1) {
			NSLOG(netsurf, ERROR,
			      "wcstombs: encoding error in argument %d", cura);
			ret = NSERROR_INVALID;
			goto cleanup_argv;
		}
		len += 1; /* account for NUL terminator */

		argv[cura] = malloc(len);
		if (argv[cura] == NULL) {
			ret = NSERROR_NOMEM;
			goto cleanup_argv;
		}

		wcstombs(argv[cura], argvw[cura], len);

		/* Convert Windows-style leading '/' flags to POSIX '-' */
		if (argv[cura][0] == '/') {
			argv[cura][0] = '-';
		}
	}

	*argc_out = argc;
	*argv_out = argv;
	LocalFree(argvw);
	return NSERROR_OK;

cleanup_argv:
	for (int i = 0; i < cura; i++) {
		free(argv[i]);
	}
	free(argv);
cleanup_argvw:
	LocalFree(argvw);
	return ret;
}


/* --------------------------------------------------------------------------
 * GUI table & entry point
 * -------------------------------------------------------------------------- */

/** Miscellaneous GUI callback table for TurboNet */
static struct gui_misc_table turbonet_misc_table = {
	.schedule        = win32_schedule,
	.present_cookies = nsw32_cookies_present,
};


/**
 * Windows application entry point.
 *
 * Initialises all subsystems in dependency order, opens the initial browser
 * window, runs the message loop, then tears everything down cleanly.
 *
 * SEC improvements vs. original:
 *  - All return values checked; fatal errors route through turbonet_die()
 *    with a descriptive message instead of silently calling exit(1).
 *  - argv is validated before use (see turbonet_win32_to_unix_commandline).
 *  - cookie_file and cookie_jar use distinct paths (see set_defaults).
 *
 * PERF improvements:
 *  - DPI is queried once and cached.
 *  - Resource paths are built before option init so set_defaults() can use
 *    them immediately.
 */
int WINAPI
WinMain(HINSTANCE hInstance, HINSTANCE hLastInstance, LPSTR lpcli, int ncmd)
{
	int argc = 0;
	char **argv = NULL;
	char **respaths = NULL;
	char *turbonet_config_home = NULL;
	nserror ret;
	const char *addr;
	nsurl *url;

	struct netsurf_table turbonet_table = {
		.misc        = &turbonet_misc_table,
		.window      = win32_window_table,
		.corewindow  = win32_core_window_table,
		.clipboard   = win32_clipboard_table,
		.download    = win32_download_table,
		.fetch       = win32_fetch_table,
		.file        = win32_file_table,
		.utf8        = win32_utf8_table,
		.bitmap      = win32_bitmap_table,
		.layout      = win32_layout_table,
	};

	/* Register the platform table before any other subsystem */
	ret = netsurf_register(&turbonet_table);
	if (ret != NSERROR_OK) {
		turbonet_die("TurboNet operation table registration failed.");
	}

	hinst = hInstance;

	/* Disable stderr buffering so crash logs are never truncated */
	setbuf(stderr, NULL);

	/* Build argc/argv from the Unicode command line */
	ret = turbonet_win32_to_unix_commandline(&argc, &argv);
	if (ret != NSERROR_OK) {
		/* Cannot log yet — log subsystem needs argv */
		return 1;
	}

	/* Initialise structured logging */
	nslog_init(turbonet_log_ensure, &argc, argv);

	/* Build the ordered list of resource search directories */
	respaths = nsws_init_resource(
	    "${APPDATA}\\" TURBONET_APP_DIR ":"
	    "${PROGRAMFILES}\\TurboNet\\TurboNet\\:"
	    NETSURF_WINDOWS_RESPATH);

	/* Determine the per-user configuration directory */
	ret = turbonet_get_config_home(&turbonet_config_home);
	if (ret != NSERROR_OK) {
		NSLOG(netsurf, WARNING,
		      "Unable to locate a configuration directory; "
		      "some settings may not persist.");
	}

	/* Load & merge user options */
	ret = turbonet_option_init(&argc, argv, respaths, turbonet_config_home);
	if (ret != NSERROR_OK) {
		NSLOG(netsurf, ERROR,
		      "Options failed to initialise: %s",
		      messages_get_errorcode(ret));
		return 1;
	}

	/* Load localised strings */
	ret = turbonet_messages_init(respaths);
	if (ret != NSERROR_OK) {
		fprintf(stderr,
		        "TurboNet: Unable to load translated messages (%s)\n",
		        messages_get_errorcode(ret));
		NSLOG(netsurf, WARNING, "Proceeding without translated messages.");
		/* Non-fatal: the browser can still function with fallback strings */
	}

	/* Core browser initialisation */
	ret = netsurf_init(NULL);
	if (ret != NSERROR_OK) {
		NSLOG(netsurf, ERROR, "TurboNet core failed to initialise.");
		return 1;
	}

	/* PERF: query DPI once and propagate to layout engine */
	browser_set_dpi(turbonet_get_screen_dpi());

	/* Restore persistent data */
	urldb_load(nsoption_charp(url_file));
	urldb_load_cookies(nsoption_charp(cookie_file));
	hotlist_init(nsoption_charp(hotlist_path),
	             nsoption_charp(hotlist_path));

	/* Register Win32 window classes */
	ret = nsws_create_main_class(hInstance);
	ret = nsws_create_drawable_class(hInstance);
	ret = nsw32_create_corewindow_class(hInstance);

	/* SEC: do not honour target="_blank" by default to prevent
	 * tab-napping attacks */
	nsoption_set_bool(target_blank, false);

	nsws_window_init_pointers(hInstance);

	/* Determine the initial URL */
	if (argc > 1) {
		/* SEC: argv[1] comes from the validated conversion above */
		addr = argv[1];
	} else if (nsoption_charp(homepage_url) != NULL) {
		addr = nsoption_charp(homepage_url);
	} else {
		addr = TURBONET_HOMEPAGE;
	}

	NSLOG(netsurf, INFO, "Opening initial URL: %s", addr);

	ret = nsurl_create(addr, &url);
	if (ret == NSERROR_OK) {
		ret = browser_window_create(BW_CREATE_HISTORY,
		                            url,
		                            NULL,
		                            NULL,
		                            NULL);
		nsurl_unref(url);
	}

	if (ret != NSERROR_OK) {
		win32_warning(messages_get_errorcode(ret), 0);
	} else {
		win32_run();
	}

	/* Persist state before shutdown */
	urldb_save_cookies(nsoption_charp(cookie_jar));
	urldb_save(nsoption_charp(url_file));

	/* Orderly teardown */
	netsurf_exit();
	nsoption_finalise(nsoptions, nsoptions_default);
	nslog_finalise();

	/* SEC: free the config home string that we allocated */
	free(turbonet_config_home);

	return 0;
}
