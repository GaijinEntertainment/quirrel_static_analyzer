#include "quirrel_lexer.h"


bool is_utf8_bom(const char * ptr, int i)
{
  return (uint8_t)ptr[i] == 0xEF && (uint8_t)ptr[i + 1] == 0xBB && (uint8_t)ptr[i + 2] == 0xBF;
}


#define STRINGIFY_MACRO(name) #name
#define TOKEN_TYPE(x, y) STRINGIFY_MACRO(x) ,
static const char * token_type_names[] =
{
  TOKEN_TYPES
  ""
};
#undef TOKEN_TYPE

#define TOKEN_TYPE(x, y) y,
const char * token_strings[] =
{
  TOKEN_TYPES
};
#undef TOKEN_TYPE


void Lexer::initializeTokenMaps()
{
  if (!tokenIdentStringToType.empty())
    return;

  for (int i = 0; i < int(TOKEN_TYPE_COUNT); i++)
    if ((token_strings[i][0] >= 'a' && token_strings[i][0] <= 'z') || token_strings[i][0] == '_')
    {
      tokenIdentStringToType.insert(std::make_pair<std::string, TokenType>(token_strings[i], TokenType(i)));
      ctx.stringList.insert(token_strings[i]);
    }
}


int Lexer::nextChar()
{
  if (index >= int(s.length()))
    return 0;

  if (index > 0 && (s[index - 1] == 0x0a || (s[index - 1] == 0x0d && s[index] != 0x0a)))
  {
    curColumn = 1;
    curLine++;
  }
  else
    curColumn++;

  int ch = uint8_t(s[index++]);
  return ch;
}

int Lexer::fetchChar(int offset)
{
  if (index + offset >= int(s.length()) || index + offset < 0)
    return 0;

  int ch = uint8_t(s[index + offset]);
  return ch;
}

bool Lexer::isSpaceOrTab(int c)
{
  return c == ' ' || c == '\t';
}

bool Lexer::isBeginOfIdent(int c)
{
  return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

bool Lexer::isContinueOfIdent(int c)
{
  return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9');
}


Lexer::Lexer(CompilationContext & compiler_context) :
  ctx(compiler_context),
  s(compiler_context.code)
{
  initializeTokenMaps();
}

Lexer::Lexer(CompilationContext & compiler_context, const std::string & code) :
  ctx(compiler_context),
  s(code)
{
  initializeTokenMaps();
}

void Lexer::print()
{
  for (int i = 0; i < int(tokens.size()); i++)
  {
    int line = 0;
    int col = 0;
   // offsetToLineAndCol(tokens[i].offset, line, col);
    const char * s = nullptr;
    char buf[64];
    if (tokens[i].type == TK_INTEGER)
      snprintf(buf, 64, "%llu", tokens[i].u.i);
    if (tokens[i].type == TK_FLOAT)
      snprintf(buf, 64, "%g", tokens[i].u.d);

    fprintf(out_stream, "%d:%d %s = '%s' \n", line, col, token_type_names[int(tokens[i].type)],
      tokens[i].type == TK_INTEGER || tokens[i].type == TK_FLOAT ? buf : tokens[i].u.s);
  }
}

std::string Lexer::expandReaderMacro(const char * str, int & out_macro_length)
{
  const char * start = str;
  char prevChar = '"';
  char curChar = 0;
  out_macro_length = 0;

  std::string macroParams;
  std::string macroStr;

  macroStr.push_back('"');

  int depth = 0;
  int braceCount = 0;
  int paramCount = 0;
  bool insideStr1 = false;
  bool insideStr2 = false;

  while (*str)
  {
    prevChar = curChar;
    curChar = *str;
    str++;

    if (prevChar != '\\')
    {
      if (!insideStr1 && !insideStr2)
      {
        if (depth > 0 && prevChar == '/' && (curChar == '/' || curChar == '*'))
        {
          ctx.error(160, "comments inside interpolated string are not supported", curLine, curColumn + int(str - start));
          return 0;
        }

        if (curChar == '{')
        {
          if (!depth)
          {
            if (macroParams.size())
              macroParams.push_back(',');

            macroParams.push_back('(');
            macroParams += "#apos:";
            macroParams += std::to_string(int(str - start));
            macroParams += " ";
            depth++;
            continue;
          }
          depth++;
        }

        if (curChar == '}')
        {
          depth--;

          if ((braceCount != 0 && depth == 0) || depth < 0)
          {
            ctx.error(161, "error in brace order", curLine, curColumn + int(str - start));
            break;
          }

          if (!depth)
          {
            macroParams.push_back(')');
            macroStr.push_back('{');
            char buf[16] = { 0 };
            snprintf(buf, sizeof(buf), "%d", paramCount);
            macroStr += buf;
            paramCount++;
          }
        }

        if (depth > 0)
        {
          if (curChar == '(' || curChar == '[')
            braceCount++;
          if (curChar == ')' || curChar == ']')
            braceCount--;
        }
      }

      if (depth > 0)
      {
        if (curChar == '"' && !insideStr1)
          insideStr2 = !insideStr2;

        if (curChar == '\'' && !insideStr2)
          insideStr1 = !insideStr1;
      }
    }
    else //  prevChar == '\'
    {
      if (curChar == '{' || curChar == '}')
      {
        if (depth == 0)
          macroStr.pop_back();
        else
          macroParams.pop_back();
      }
    }

    if (depth == 0)
      macroStr.push_back(curChar);
    else
      macroParams.push_back(curChar);

    if (depth <= 0 && curChar == '"' && prevChar != '\\' && !insideStr1 && !insideStr2)
      break;

    if (curChar == '\\' && prevChar == '\\')
      curChar = '\0';
  }

  if (macroParams.size() != 0)
  {
    macroStr += ".subst(";

    for (size_t i = 0; i < macroParams.size(); i++)
      macroStr.push_back(macroParams[i]);

    macroStr.push_back(')');
  }
  macroStr += "#apos:";
  macroStr += std::to_string(int(str - start));
  macroStr += " ";


  out_macro_length = int(str - start);

  return macroStr;
}

bool Lexer::parseStringLiteral(bool raw_string, int open_char)
{
  std::string tok;
  insideString = true;
  int beginColumn = curColumn;
  int beginLine = curLine;
  int ch = 0;

  for (ch = nextChar(); ch > 0 && !ctx.isError; ch = nextChar())
  {
    if (ch == open_char)
    {
      if (raw_string && fetchChar() == '\"')
      {
        ch = nextChar();
      }
      else
      {
        insideString = false;
        break;
      }
    }
    else if (ch == 0x0d || ch == 0x0a)
    {
      if (!raw_string)
      {
        ctx.error(101, "end of line inside string literal", curLine, curColumn);
        insideString = false;
        return false;
      }

      if (ch == 0x0d && fetchChar() == 0x0a)
      {
        nextChar();
        ch = '\n';
      }
    }
    else if (ch == '\\' && !raw_string)
    {
      ch = nextChar();
      switch (ch)
      {
      case '\\': ch = '\\'; break;
      case 'a': ch = '\a'; break;
      case 'b': ch = '\b'; break;
      case 'n': ch = '\n'; break;
      case 'r': ch = '\r'; break;
      case 'v': ch = '\v'; break;
      case 't': ch = '\t'; break;
      case 'f': ch = '\f'; break;
      case '0': ch = '\0'; break;
      case '\"': ch = '\"'; break;
      case '\'': ch = '\''; break;
      case 'x':
      case 'u':
      case 'U':
      {
        int digitsLimit = INT_MAX;
        if (ch == 'u')
          digitsLimit = 4;
        if (ch == 'U')
          digitsLimit = 8;

        std::string hex;

        for (ch = fetchChar(); ch > 0; ch = fetchChar())
        {
          if (!isxdigit(ch))
            break;
          hex += char(ch);
          nextChar();

          digitsLimit--;
          if (digitsLimit <= 0)
            break;
        }

        if (hex.empty())
        {
          ctx.error(102, "hexadecimal number expected", curLine, curColumn);
          break;
        }

        ch = (int)strtoull(hex.c_str(), nullptr, 16);
      }
      break;

      default:
        ctx.error(103, "unrecognised escaper char", curLine, curColumn);
        return false;
      }
    }

    tok += char(ch);
  }

  if (open_char == '\'')
  {
    if (tok.empty())
    {
      ctx.error(104, "empty constant", curLine, curColumn);
      return false;
    }

    if (tok.length() > 1)
    {
      ctx.error(105, "constant is too long", curLine, curColumn);
      return false;
    }

    Token::U u;
    u.i = (unsigned char)tok[0];
    tokens.push_back({ (TokenType)TK_INTEGER, false, false, (unsigned short)beginColumn, beginLine, u });
  }
  else
  {
    ctx.stringList.insert(tok);
    auto listIt = ctx.stringList.find(tok);
    Token::U u;
    u.s = listIt->c_str();
    tokens.push_back({ (TokenType)TK_STRING_LITERAL, false, false, (unsigned short)beginColumn, beginLine, u });
  }

  return true;
}


void Lexer::onCompilerDirective(const std::string & directive)
{
  const char * s = directive.c_str();
  if (strstr(s, "#apos:") == s)
  {
    s += 6;
    sscanf(s, "%d", &curColumn);
    curColumn--;
  }
}

bool Lexer::process()
{
  tokens.clear();
  index = is_utf8_bom(s.c_str(), 0) ? 3 : 0;

  curLine = 1;
  curColumn = 1;

  insideComment = false;
  insideString = false;
  insideRawString = false;

  #define PUSH_TOKEN(tk) \
    { \
      Token::U u; u.s = token_strings[tk]; tokens.push_back( \
      { (TokenType)(tk), false, false, \
        (unsigned short)curColumn, curLine, u \
      }); \
    }

  for (int ch = nextChar(); ch > 0 && !ctx.isError; ch = nextChar())
    switch (ch)
    {
    case ' ':
    case '\t':
      if (!tokens.empty())
        tokens.back().nextSpace = true;
      break;

    case 0x0d:
    case 0x0a:
      if (!tokens.empty())
        tokens.back().nextEol = true;
      break;

    case '/':
      if (fetchChar() == '/')
      {
        for (ch = nextChar(); ch > 0 && ch != '\n'; ch = nextChar())
          ;
        if (!tokens.empty())
          tokens.back().nextEol = true;
      }
      else if (fetchChar() == '*')
      {
        nextChar();
        nextChar();
        insideComment = true;
        bool eol = false;
        for (ch = nextChar(); ch > 0; ch = nextChar())
        {
          if (ch == '\n')
            eol = true;
          if (ch == '/' && fetchChar(-2) == '*')
          {
            insideComment = false;
            break;
          }
        }

        if (eol)
          if (!tokens.empty())
            tokens.back().nextEol = true;
      }
      else if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_DIVEQ);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_DIV);
      }
      break;

    case '#':
      {
        std::string tok;
        tok += char(ch);
        for (ch = fetchChar(); ch > 0; ch = fetchChar())
        {
          if (isalnum(ch) || ch == '_' || ch == '-' || ch == ':')
          {
            tok += char(ch);
            nextChar();
          }
          else
            break;
        }

        onCompilerDirective(tok);
      }
      break;

    case '@':
      if (fetchChar() == '@' && fetchChar(1) == '\"')
      {
        nextChar();
        nextChar();
        if (parseStringLiteral(true, '\"'))
        {
          Token &lastToken = tokens[tokens.size() - 1];
          if (lastToken.type != TK_STRING_LITERAL)
            ctx.error(128, "error parsing docstring", curLine, curColumn);
          else
            lastToken.type = TK_DOCSTRING;
        }
      }
      else if (fetchChar() == '\"')
      {
        nextChar();
        parseStringLiteral(true, '\"');
      }
      else
        PUSH_TOKEN(TK_AT);
      break;

    case '\'':
      parseStringLiteral(false, '\'');
      break;

    case '\"':
      if (tokens.size() > 0 && tokens[tokens.size() - 1].type == TK_READER_MACRO)
      {
        int macroLength = 0;
        std::string macro = expandReaderMacro(s.c_str() + index, macroLength);
        index += macroLength;
        int baseColumn = tokens[tokens.size() - 1].column;
        int line = tokens[tokens.size() - 1].line;
        Lexer * macroLex = new Lexer(ctx, macro);
        if (macroLex->process() && !macroLex->tokens.empty())
        {
          for (auto & t : macroLex->tokens)
          {
            t.column += baseColumn;
            t.line = line;
          }

          tokens.erase(tokens.end() - 1, tokens.end());
          tokens.insert(tokens.end(), macroLex->tokens.begin(), macroLex->tokens.end() - 1);
          tokens[tokens.size() - 1].nextEol = false;
        }
        delete macroLex;
      }
      else
        parseStringLiteral(false, '\"');

      break;

    case '-':
      if (fetchChar() == '-')
      {
        PUSH_TOKEN(TK_MINUSMINUS);
        nextChar();
      }
      else if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_MINUSEQ);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_MINUS);
      }
      break;

    case '+':
      if (fetchChar() == '+')
      {
        PUSH_TOKEN(TK_PLUSPLUS);
        nextChar();
      }
      else if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_PLUSEQ);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_PLUS);
      }
      break;

    case '!':
      if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_NE);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_NOT);
      }
      break;

    case '%':
      if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_MODEQ);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_MODULO);
      }
      break;

    case '&':
      if (fetchChar() == '&')
      {
        PUSH_TOKEN(TK_AND);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_BITAND);
      }
      break;

    case '=':
      if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_EQ);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_ASSIGN);
      }
      break;

    case '(':
      PUSH_TOKEN(TK_LPAREN);
      break;

    case ')':
      PUSH_TOKEN(TK_RPAREN);
      break;

    case ',':
      PUSH_TOKEN(TK_COMMA);
      break;

    case '[':
      PUSH_TOKEN(TK_LSQUARE);
      break;

    case ']':
      PUSH_TOKEN(TK_RSQUARE);
      break;

    case '{':
      PUSH_TOKEN(TK_LBRACE);
      break;

    case '}':
      PUSH_TOKEN(TK_RBRACE);
      break;

    case '^':
      PUSH_TOKEN(TK_BITXOR);
      break;

    case '~':
      PUSH_TOKEN(TK_INV);
      break;

    case '$':
      PUSH_TOKEN(TK_READER_MACRO);
      break;

    case ';':
      PUSH_TOKEN(TK_SEMICOLON);
      break;

    case '*':
      if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_MULEQ);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_MUL);
      }
      break;

    case '.':
      if (fetchChar() == '.' && fetchChar(1) != '.')
      {
        ctx.error(106, "invalid token '..'", curLine, curColumn);
      }
      else if (fetchChar() == '.' && fetchChar(1) == '.')
      {
        PUSH_TOKEN(TK_VARPARAMS);
        nextChar();
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_DOT);
      }
      break;

    case ':':
      if (fetchChar() == ':')
      {
        PUSH_TOKEN(TK_DOUBLE_COLON);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_COLON);
      }
      break;

    case '?':
      if (fetchChar() == '(')
      {
        PUSH_TOKEN(TK_NULLCALL);
        nextChar();
      }
      else if (fetchChar() == '?')
      {
        PUSH_TOKEN(TK_NULLCOALESCE);
        nextChar();
      }
      else if (fetchChar() == '[')
      {
        PUSH_TOKEN(TK_NULLGETOBJ);
        nextChar();
      }
      else if (fetchChar() == '(')
      {
        PUSH_TOKEN(TK_NULLCALL);
        nextChar();
      }
      else if (fetchChar() == '.')
      {
        PUSH_TOKEN(TK_NULLGETSTR);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_QMARK);
      }
      break;;

    case '|':
      if (fetchChar() == '|')
      {
        PUSH_TOKEN(TK_OR);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_BITOR);
      }
      break;

    case '<':
      if (fetchChar() == '=')
      {
        if (fetchChar(1) == '>')
        {
          PUSH_TOKEN(TK_3WAYSCMP);
          nextChar();
        }
        else
        {
          PUSH_TOKEN(TK_LE);
        }
        nextChar();
      }
      else if (fetchChar() == '-')
      {
        PUSH_TOKEN(TK_NEWSLOT);
        nextChar();
      }
      else if (fetchChar() == '<')
      {
        PUSH_TOKEN(TK_SHIFTL);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_LS);
      }
      break;

    case '>':
      if (fetchChar() == '>')
      {
        if (fetchChar(1) == '>')
        {
          PUSH_TOKEN(TK_USHIFTR);
          nextChar();
        }
        else
        {
          PUSH_TOKEN(TK_SHIFTR);
        }
        nextChar();
      }
      else if (fetchChar() == '=')
      {
        PUSH_TOKEN(TK_GE);
        nextChar();
      }
      else
      {
        PUSH_TOKEN(TK_GT);
      }
      break;

      default:
        if (isBeginOfIdent(ch))
        {
          std::string tok;
          tok += char(ch);
          int beginLine = curLine;
          int beginColumn = curColumn;
          for (ch = fetchChar(); ch > 0; ch = fetchChar())
          {
            if (isContinueOfIdent(ch))
            {
              tok += char(ch);
              nextChar();
            }
            else
              break;
          }

          ctx.stringList.insert(tok);
          auto listIt = ctx.stringList.find(tok);
          Token::U u;
          u.s = listIt->c_str();

          auto it = tokenIdentStringToType.find(tok);
          if (it != tokenIdentStringToType.end())
            tokens.push_back({ it->second, false, false, (unsigned short)beginColumn, beginLine, u });
          else
            tokens.push_back({ (TokenType)TK_IDENTIFIER, false, false, (unsigned short)beginColumn, beginLine, u });
        }
        else if (isdigit(ch))
        {
          std::string tok;
          tok += char(ch);
          int beginLine = curLine;
          int beginColumn = curColumn;
          bool hasPoint = false;
          bool hasExp = false;

          Token::U u;
          u.i = 0;

          if (ch == '0' && isdigit(fetchChar()))
          {
            ctx.error(107, "octal numbers are not supported", curLine, curColumn);
            break;
          }
          else if (ch == '0' && toupper(fetchChar()) == 'X')
          {
            tok += nextChar();
            for (ch = fetchChar(); ch > 0; ch = fetchChar())
            {
              if (isxdigit(ch))
              {
                tok += char(ch);
                nextChar();
              }
              else
                break;
            }
          }
          else
          {
            for (ch = fetchChar(); ch > 0; ch = fetchChar())
            {
              if (isdigit(ch) || ch == '.' || ch == 'e' || ch == 'E')
              {
                nextChar();
                tok += char(ch);
                if (ch == '.')
                {
                  if (hasPoint || hasExp)
                  {
                    ctx.error(108, "error in number", curLine, curColumn);
                    break;
                  }
                  hasPoint = true;
                }
                else if (ch == 'e' || ch == 'E')
                {
                  if (hasExp)
                  {
                    ctx.error(108, "error in number", curLine, curColumn);
                    break;
                  }
                  hasExp = true;
                  ch = nextChar();
                  tok += char(ch);
                  if (ch != '+' && ch != '-' && !isdigit(ch))
                  {
                    ctx.error(108, "error in number", curLine, curColumn);
                    break;
                  }

                  if (!isdigit(ch))
                  {
                    ch = nextChar();
                    tok += char(ch);
                    if (!isdigit(ch))
                    {
                      ctx.error(108, "error in number", curLine, curColumn);
                      break;
                    }
                  }
                }
              }
              else
                break;
            }
          }

          if (isBeginOfIdent(ch))
          {
            ctx.error(108, "error in number", curLine, curColumn);
            break;
          }

          if (hasExp || hasPoint)
          {
            u.d = strtod(tok.c_str(), nullptr);
            tokens.push_back({ TK_FLOAT, false, false, (unsigned short)beginColumn, beginLine, u });
          }
          else
          {
            if (tok.length() >= 2 && toupper(tok[1]) == 'X')
            {
              if (tok.length() == 2)
              {
                ctx.error(109, "expected hex number", curLine, curColumn);
                break;
              }

              u.i = strtoull(tok.c_str() + 2, nullptr, 16);
              if (tok.length() > 16 + 2)
              {
                ctx.error(110, "too many digits for a hex number", curLine, curColumn);
                break;
              }
            }
            else
            {
              u.i = strtoull(tok.c_str(), nullptr, 10);
              if (u.i > LLONG_MAX)
              {
                ctx.error(111, "integer number is too big", curLine, curColumn);
              }
            }
            tokens.push_back({ (TokenType)TK_INTEGER, false, false, (unsigned short)beginColumn, beginLine, u });
          }
        }
        else
        {
          ctx.error(112, "syntax error", curLine, curColumn);
        }
      break;

    } // switch


  if (!ctx.isError)
  {
    if (insideComment)
      ctx.error(113, "unexpected end of file inside comment", curLine, curColumn);
    else if (insideString)
      ctx.error(114, "unexpected end of file inside string", curLine, curColumn);
    else if (insideRawString)
      ctx.error(115, "unexpected end of file inside raw string", curLine, curColumn);
  }

  if (!ctx.isError)
  {
    if (!tokens.empty())
      tokens.back().nextEol = true;

    PUSH_TOKEN(TK_EOF);
  }

  return !ctx.isError;
}


