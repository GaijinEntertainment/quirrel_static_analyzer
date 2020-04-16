#pragma once

#include <set>
#include <string>
#include <vector>
#include <stdio.h>

bool is_utf8_bom(const char * ptr, int i);

extern FILE * out_stream;

struct Token;

enum OutputMode
{
  OM_1_LINE, // 1 line per warning
  OM_2_LINES,
  OM_FULL,
};

enum ErrorLevels
{
  ERRORLEVEL_WARNING = 2,
  ERRORLEVEL_ERROR = 3,
  ERRORLEVEL_FATAL = 4,
};

struct CompilerMessage
{
  int line;
  int column;
  int intId;
  const char * textId;
  std::string message;
  std::string fileName;
  bool isError;

  CompilerMessage()
  {
    line = 0;
    column = 0;
    intId = 0;
    textId = "";
    isError = false;
  }
};

class CompilationContext
{
  std::vector<int> suppressWarnings;
  static std::set<std::string> shownMessages;
  static int errorLevel;

public:

  class Poolable
  {
    CompilationContext & ctx;
  public:
    Poolable(CompilationContext & ctx_) : ctx(ctx_)
    {
      ctx.poolableObjects.push_back(this);
    }
  };

  std::vector<Poolable *> poolableObjects;
  std::set<std::string> stringList;
  std::string fileName;
  std::string fileDir;
  std::string code;
  std::vector<int> shownWarningsAndErrors;
  static std::vector<CompilerMessage> compilerMessages;
  static const char * redirectMessagesToJson;
  static void setErrorLevel(int error_level);
  static int getErrorLevel();
  static void clearErrorLevel();
  bool isError;
  bool isWarning;
  OutputMode outputMode;

  CompilationContext();
  ~CompilationContext();
  void setFileName(const std::string & file_name);
  void getNearestStrings(int line_num, std::string & nearest_strings, std::string & cur_string) const;
  void error(int error_code, const char * error, int line, int col);
  static void globalError(const char * error);
  void warning(const char * text_id, int line, int col);
  void warning(const char * text_id, const Token & tok, const char * arg0 = "???", const char * arg1 = "???",
    const char * arg2 = "???", const char * arg3 = "???");
  void offsetToLineAndCol(int offset, int & line, int & col) const;
  void clearSuppressedWarnings();
  void suppressWaring(int intId);
  void suppressWaring(const char * textId);
  bool isWarningSuppressed(const char * text_id);
  void inverseWarningsSuppression();
  static void printAllWarningsList();
};

