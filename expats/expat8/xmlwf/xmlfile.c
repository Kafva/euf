/*
                            __  __            _
                         ___\ \/ /_ __   __ _| |_
                        / _ \\  /| '_ \ / _` | __|
                       |  __//  \| |_) | (_| | |_
                        \___/_/\_\ .__/ \__,_|\__|
                                 |_| XML parser

   Copyright (c) 1997-2000 Thai Open Source Software Center Ltd
   Copyright (c) 2000      Clark Cooper <coopercc@users.sourceforge.net>
   Copyright (c) 2002-2003 Fred L. Drake, Jr. <fdrake@users.sourceforge.net>
   Copyright (c) 2004-2006 Karl Waclawek <karl@waclawek.net>
   Copyright (c) 2005-2007 Steven Solie <steven@solie.ca>
   Copyright (c) 2016-2021 Sebastian Pipping <sebastian@pipping.org>
   Copyright (c) 2017      Rhodri James <rhodri@wildebeest.org.uk>
   Copyright (c) 2019      David Loffredo <loffredo@steptools.com>
   Copyright (c) 2021      Dong-hee Na <donghee.na@python.org>
   Licensed under the MIT license:

   Permission is  hereby granted,  free of charge,  to any  person obtaining
   a  copy  of  this  software   and  associated  documentation  files  (the
   "Software"),  to  deal in  the  Software  without restriction,  including
   without  limitation the  rights  to use,  copy,  modify, merge,  publish,
   distribute, sublicense, and/or sell copies of the Software, and to permit
   persons  to whom  the Software  is  furnished to  do so,  subject to  the
   following conditions:

   The above copyright  notice and this permission notice  shall be included
   in all copies or substantial portions of the Software.

   THE  SOFTWARE  IS  PROVIDED  "AS  IS",  WITHOUT  WARRANTY  OF  ANY  KIND,
   EXPRESS  OR IMPLIED,  INCLUDING  BUT  NOT LIMITED  TO  THE WARRANTIES  OF
   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN
   NO EVENT SHALL THE AUTHORS OR  COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
   DAMAGES OR  OTHER LIABILITY, WHETHER  IN AN  ACTION OF CONTRACT,  TORT OR
   OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE
   USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

#include <expat_config.h>

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <fcntl.h>

#ifdef _WIN32
#  include "winconfig.h"
#endif

#include "expat.h"
#include "internal.h" /* for UNUSED_P only */
#include "xmlfile.h"
#include "xmltchar.h"
#include "filemap.h"

#if defined(_MSC_VER)
#  include <io.h>
#endif

#ifdef HAVE_UNISTD_H
#  include <unistd.h>
#endif

#ifndef O_BINARY
#  ifdef _O_BINARY
#    define O_BINARY _O_BINARY
#  else
#    define O_BINARY 0
#  endif
#endif

#ifdef _DEBUG
#  define READ_SIZE 16
#else
#  define READ_SIZE (1024 * 8)
#endif

typedef struct {
  XML_Parser parser;
  int *retPtr;
} PROCESS_ARGS;

static int processStream_old_b026324c6904b2a(const XML_Char *filename, XML_Parser parser);

static void
reportError_old_b026324c6904b2a(XML_Parser parser, const XML_Char *filename) {
  enum XML_Error code = XML_GetErrorCode_old_b026324c6904b2a(parser);
  const XML_Char *message = XML_ErrorString_old_b026324c6904b2a(code);
  if (message)
    ftprintf(stdout,
             T("%s") T(":%") T(XML_FMT_INT_MOD) T("u") T(":%")
                 T(XML_FMT_INT_MOD) T("u") T(": %s\n"),
             filename, XML_GetErrorLineNumber(parser),
             XML_GetErrorColumnNumber(parser), message);
  else
    ftprintf(stderr, T("%s: (unknown message %d)\n"), filename, code);
}

/* This implementation will give problems on files larger than INT_MAX. */
static void
processFile_old_b026324c6904b2a(const void *data, size_t size, const XML_Char *filename,
            void *args) {
  XML_Parser parser = ((PROCESS_ARGS *)args)->parser;
  int *retPtr = ((PROCESS_ARGS *)args)->retPtr;
  if (XML_Parse_old_b026324c6904b2a(parser, (const char *)data, (int)size, 1) == XML_STATUS_ERROR) {
    reportError_old_b026324c6904b2a(parser, filename);
    *retPtr = 0;
  } else
    *retPtr = 1;
}

#if defined(_WIN32)

static int
isAsciiLetter(XML_Char c) {
  return (T('a') <= c && c <= T('z')) || (T('A') <= c && c <= T('Z'));
}

#endif /* _WIN32 */

static const XML_Char *
resolveSystemId_old_b026324c6904b2a(const XML_Char *base, const XML_Char *systemId,
                XML_Char **toFree) {
  XML_Char *s;
  *toFree = 0;
  if (! base || *systemId == T('/')
#if defined(_WIN32)
      || *systemId == T('\\')
      || (isAsciiLetter(systemId[0]) && systemId[1] == T(':'))
#endif
  )
    return systemId;
  *toFree = (XML_Char *)malloc((tcslen(base) + tcslen(systemId) + 2)
                               * sizeof(XML_Char));
  if (! *toFree)
    return systemId;
  tcscpy(*toFree, base);
  s = *toFree;
  if (tcsrchr(s, T('/')))
    s = tcsrchr(s, T('/')) + 1;
#if defined(_WIN32)
  if (tcsrchr(s, T('\\')))
    s = tcsrchr(s, T('\\')) + 1;
#endif
  tcscpy(s, systemId);
  return *toFree;
}

static int
externalEntityRefFilemap_old_b026324c6904b2a(XML_Parser parser, const XML_Char *context,
                         const XML_Char *base, const XML_Char *systemId,
                         const XML_Char *publicId) {
  int result;
  XML_Char *s;
  const XML_Char *filename;
  XML_Parser entParser = XML_ExternalEntityParserCreate_old_b026324c6904b2a(parser, context, 0);
  int filemapRes;
  PROCESS_ARGS args;
  UNUSED_P(publicId);
  args.retPtr = &result;
  args.parser = entParser;
  filename = resolveSystemId_old_b026324c6904b2a(base, systemId, &s);
  XML_SetBase_old_b026324c6904b2a(entParser, filename);
  filemapRes = filemap_old_b026324c6904b2a(filename, processFile_old_b026324c6904b2a, &args);
  switch (filemapRes) {
  case 0:
    result = 0;
    break;
  case 2:
    ftprintf(stderr,
             T("%s: file too large for memory-mapping")
                 T(", switching to streaming\n"),
             filename);
    result = processStream_old_b026324c6904b2a(filename, entParser);
    break;
  }
  free(s);
  XML_ParserFree_old_b026324c6904b2a(entParser);
  return result;
}

static int
processStream_old_b026324c6904b2a(const XML_Char *filename, XML_Parser parser) {
  /* passing NULL for filename means read input from stdin */
  int fd = 0; /* 0 is the fileno for stdin */

  if (filename != NULL) {
    fd = topen(filename, O_BINARY | O_RDONLY);
    if (fd < 0) {
      tperror(filename);
      return 0;
    }
  }
  for (;;) {
    int nread;
    char *buf = (char *)XML_GetBuffer_old_b026324c6904b2a(parser, READ_SIZE);
    if (! buf) {
      if (filename != NULL)
        close(fd);
      ftprintf(stderr, T("%s: out of memory\n"),
               filename != NULL ? filename : T("xmlwf"));
      return 0;
    }
    nread = read(fd, buf, READ_SIZE);
    if (nread < 0) {
      tperror(filename != NULL ? filename : T("STDIN"));
      if (filename != NULL)
        close(fd);
      return 0;
    }
    if (XML_ParseBuffer_old_b026324c6904b2a(parser, nread, nread == 0) == XML_STATUS_ERROR) {
      reportError_old_b026324c6904b2a(parser, filename != NULL ? filename : T("STDIN"));
      if (filename != NULL)
        close(fd);
      return 0;
    }
    if (nread == 0) {
      if (filename != NULL)
        close(fd);
      break;
      ;
    }
  }
  return 1;
}

static int
externalEntityRefStream_old_b026324c6904b2a(XML_Parser parser, const XML_Char *context,
                        const XML_Char *base, const XML_Char *systemId,
                        const XML_Char *publicId) {
  XML_Char *s;
  const XML_Char *filename;
  int ret;
  XML_Parser entParser = XML_ExternalEntityParserCreate_old_b026324c6904b2a(parser, context, 0);
  UNUSED_P(publicId);
  filename = resolveSystemId_old_b026324c6904b2a(base, systemId, &s);
  XML_SetBase_old_b026324c6904b2a(entParser, filename);
  ret = processStream_old_b026324c6904b2a(filename, entParser);
  free(s);
  XML_ParserFree_old_b026324c6904b2a(entParser);
  return ret;
}

int
XML_ProcessFile_old_b026324c6904b2a(XML_Parser parser, const XML_Char *filename, unsigned flags) {
  int result;

  if (! XML_SetBase_old_b026324c6904b2a(parser, filename)) {
    ftprintf(stderr, T("%s: out of memory"), filename);
    exit(1);
  }

  if (flags & XML_EXTERNAL_ENTITIES)
    XML_SetExternalEntityRefHandler_old_b026324c6904b2a(parser, (flags & XML_MAP_FILE)
                                                ? externalEntityRefFilemap_old_b026324c6904b2a
                                                : externalEntityRefStream_old_b026324c6904b2a);
  if (flags & XML_MAP_FILE) {
    int filemapRes;
    PROCESS_ARGS args;
    args.retPtr = &result;
    args.parser = parser;
    filemapRes = filemap_old_b026324c6904b2a(filename, processFile_old_b026324c6904b2a, &args);
    switch (filemapRes) {
    case 0:
      result = 0;
      break;
    case 2:
      ftprintf(stderr,
               T("%s: file too large for memory-mapping")
                   T(", switching to streaming\n"),
               filename);
      result = processStream_old_b026324c6904b2a(filename, parser);
      break;
    }
  } else
    result = processStream_old_b026324c6904b2a(filename, parser);
  return result;
}
