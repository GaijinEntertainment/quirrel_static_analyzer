#include "quirrel_parser.h"

using namespace std;

#define NODE_TYPE(x, y) y,
const char * node_type_names[] =
{
  NODE_TYPES
};
#undef NODE_TYPE

static Token emptyToken;

struct Parser
{
  CompilationContext & ctx;
  int pos;

  enum ExpressionContext
  {
    EC_USUAL = 0,
    EC_CONDITION,
  };
  vector<ExpressionContext> expressionContext;

  Lexer & lexer;
  vector<Token> & tokens;
  Token * tok;

  Parser(Lexer & lexer_) :
    lexer(lexer_),
    tokens(lexer_.tokens),
    ctx(lexer_.getCompilationContext())
  {
    pos = 0;
    tok = tokens.empty() ? &emptyToken : &tokens[pos];
    expressionContext.push_back(EC_USUAL);
  }


#define EXPRESSION_CONTEXT_SCOPE(ctx) \
    struct ExprContextScope \
    { \
      vector<ExpressionContext> & ec; \
      ExprContextScope(vector<ExpressionContext> & expressionContext) : ec(expressionContext) { ec.push_back(ctx); } \
      ~ExprContextScope() { ec.pop_back(); } \
    } exprContextScope(expressionContext);

  bool expect(TokenType token_type)
  {
    if (tokens[pos].type == token_type)
    {
      tok = &tokens[pos];
      pos++;
      return true;
    }
    ctx.error(117, (string("expected '") + token_strings[token_type] + "', but '" + token_strings[tokens[pos].type] +
      "' found").c_str(), tokens[pos].line, tokens[pos].column);
    return false;
  }

  bool accept(TokenType token_type)
  {
    if (tokens[pos].type == token_type)
    {
      tok = &tokens[pos];
      pos++;
      return true;
    }
    return false;
  }

  TokenType forwardToken(int offset)
  {
    if (pos + offset >= int(tokens.size()))
      return TK_EOF;
    else
      return tokens[pos + offset].type;
  }

  Token & prevToken()
  {
    return tokens[pos > 2 ? pos - 2 : 0];
  }

  Node * createOperandNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    switch (t.type)
    {
    case TK_NULL:
      n->nodeType = PNT_NULL;
      break;

    case TK_TRUE:
    case TK_FALSE:
      n->nodeType = PNT_BOOL;
      break;

    case TK_STRING_LITERAL:
      n->nodeType = PNT_STRING;
      break;

    case TK_FLOAT:
      n->nodeType = PNT_FLOAT;
      break;

    case TK_INTEGER:
      n->nodeType = PNT_INTEGER;
      break;

    default:
      return nullptr;
    }
    return n;
  }

  Node * createEmptyStatementNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_EMPTY_STATEMENT;
    return n;
  }

  Node * createIdentifierNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_IDENTIFIER;
    return n;
  }

  Node * createDocStringNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_DOCSTRING;
    return n;
  }

  Node * createVarParamsNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_VAR_PARAMS;
    return n;
  }

  Node * createRootNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_ROOT;
    return n;
  }

  Node * createThisNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_THIS;
    return n;
  }

  Node * createReturnNode(Token & t, Node * optional_result)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_RETURN;
    if (optional_result)
      n->children.push_back(optional_result);
    return n;
  }

  Node * createYieldNode(Token & t, Node * optional_result)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_YIELD;
    if (optional_result)
      n->children.push_back(optional_result);
    return n;
  }

  Node * createBreakNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_BREAK;
    return n;
  }

  Node * createContinueNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_CONTINUE;
    return n;
  }

  Node * createThrowNode(Token & t, Node * expression)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_THROW;
    n->children.push_back(expression);
    return n;
  }

  Node * createTryCatchNode(Token & t, Node * try_body, Node * id, Node * catch_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_TRY_CATCH;
    n->children.push_back(try_body);
    n->children.push_back(id);
    n->children.push_back(catch_body);
    return n;
  }

  Node * createConstDeclarationNode(Token & t, Node * name, Node * value, bool is_global)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = is_global ? PNT_GLOBAL_CONST_DECLARATION : PNT_CONST_DECLARATION;
    n->children.push_back(name);
    n->children.push_back(value);
    return n;
  }

  Node * createSwitchNode(Token & t, Node * expression, vector<Token *> case_tests_tokens,
    vector<Node *> case_tests, vector<Node *> statements)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_SWITCH_STATEMENT;
    n->children.push_back(expression);
    for (size_t i = 0; i < case_tests_tokens.size(); i++)
    {
      Node * switchCase = new Node(ctx, *case_tests_tokens[i]);
      switchCase->nodeType = PNT_SWITCH_CASE;
      switchCase->children.push_back(case_tests[i]);
      switchCase->children.push_back(statements[i]);
      n->children.push_back(switchCase);
    }
    return n;
  }

  Node * createLocalVarDeclarationNode(Token & t, vector<Node *> var_keys, vector<Node *> optional_values)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_LOCAL_VAR_DECLARATION;

    for (size_t i = 0; i < var_keys.size(); i++)
    {
      Node * declarator = new Node(ctx, var_keys[i]->tok);
      declarator->nodeType = PNT_VAR_DECLARATOR;
      declarator->children.push_back(var_keys[i]);
      if (optional_values[i])
        declarator->children.push_back(optional_values[i]);
      n->children.push_back(declarator);
    }

    return n;
  }

  Node * createImportVarDeclarationNode(vector<Node *> var_keys)
  {
    Node * n = new Node(ctx, emptyToken);
    n->nodeType = PNT_IMPORT_VAR_DECLARATION;

    for (size_t i = 0; i < var_keys.size(); i++)
    {
      Node * declarator = new Node(ctx, var_keys[i]->tok);
      declarator->nodeType = PNT_VAR_DECLARATOR;
      declarator->children.push_back(var_keys[i]);
      n->children.push_back(declarator);
    }

    return n;
  }

  Node * createInexprVarDeclaratorNode(Token & t, Node * key, Node * value)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_INEXPR_VAR_DECLARATOR;
    n->children.push_back(key);
    n->children.push_back(value);
    return n;
  }

  Node * createAccessMemberNode(Token & t, Node * container, Node * key)
  {
    if (!container || !key)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_ACCESS_MEMBER;
    n->children.push_back(container);
    n->children.push_back(key);
    return n;
  }

  Node * createAccessMemberIfNotNullNode(Token & t, Node * container, Node * key)
  {
    if (!container || !key)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_ACCESS_MEMBER_IF_NOT_NULL;
    n->children.push_back(container);
    n->children.push_back(key);
    return n;
  }

  Node * createIfElseNode(Token & t, Node * expression, Node * if_true, Node * optional_if_false)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_IF_ELSE;
    n->children.push_back(expression);
    n->children.push_back(if_true);
    if (optional_if_false)
      n->children.push_back(optional_if_false);
    return n;
  }

  Node * createWhileLoopNode(Token & t, Node * expression, Node * loop_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_WHILE_LOOP;
    n->children.push_back(expression);
    n->children.push_back(loop_body);
    return n;
  }

  Node * createDoWhileLoopNode(Token & t, Node * expression, Node * loop_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_DO_WHILE_LOOP;
    n->children.push_back(expression);
    n->children.push_back(loop_body);
    return n;
  }

  Node * createForLoopNode(Token & t, Node * optional_initialization, Node * optional_expression,
    Node * optional_increment, Node * loop_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_FOR_LOOP;
    n->children.push_back(optional_initialization);
    n->children.push_back(optional_expression);
    n->children.push_back(optional_increment);
    n->children.push_back(loop_body);
    return n;
  }

  Node * createForEachLoopNode(Token & t, Node * variable, Node * optional_index, Node * container, Node * loop_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_FOR_EACH_LOOP;
    n->children.push_back(variable);
    n->children.push_back(optional_index);
    n->children.push_back(container);
    n->children.push_back(loop_body);
    return n;
  }

  Node * createCallNode(Token & t, Node * function, vector<Node *> & params)
  {
    if (!function)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_FUNCTION_CALL;
    n->children.push_back(function);
    for (size_t i = 0; i < params.size(); i++)
      n->children.push_back(params[i]);
    return n;
  }

  Node * createCallIfNotNullNode(Token & t, Node * function, vector<Node *> & params)
  {
    if (!function)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_FUNCTION_CALL_IF_NOT_NULL;
    n->children.push_back(function);
    for (size_t i = 0; i < params.size(); i++)
      n->children.push_back(params[i]);
    return n;
  }

  Node * createArrayCreationNode(Token & t, vector<Node *> & params)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_ARRAY_CREATION;
    n->children = params;
    return n;
  }

  Node * createTableCreationNode(Token & t, vector<Node *> & keys, vector<Node *> & values, vector<Token *> & assignment_tokens)
  {
    std::vector<Node *> keyvalues;
    for (size_t i = 0; i < keys.size(); i++)
    {
      Node * keyvalue = new Node(ctx, *assignment_tokens[i]);
      keyvalue->nodeType = PNT_KEY_VALUE;
      keyvalue->children.push_back(keys[i]);
      keyvalue->children.push_back(values[i]);
      keyvalues.push_back(keyvalue);
    }

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_TABLE_CREATION;
    n->children = keyvalues;
    return n;
  }

  Node * createReaderMacroOpNode(Token & t, Node * applied_to)
  {
    if (!applied_to)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_READER_MACRO;
    n->children.push_back(applied_to);
    return n;
  }

  Node * createUnaryPreOpNode(Token & t, Node * applied_to)
  {
    if (!applied_to)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_UNARY_PRE_OP;
    n->children.push_back(applied_to);
    return n;
  }

  Node * createUnaryPostOpNode(Token & t, Node * applied_to)
  {
    if (!applied_to)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_UNARY_POST_OP;
    n->children.push_back(applied_to);
    return n;
  }

  Node * createBinaryOpNode(Token & t, Node * left, Node * right)
  {
    if (!left || !right)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_BINARY_OP;
    n->children.push_back(left);
    n->children.push_back(right);
    return n;
  }

  Node * createTernaryOpNode(Token & t, Node * expr, Node * if_true, Node * if_false)
  {
    if (!expr || !if_true || !if_false)
      return nullptr;

    Node * n = new Node(ctx, t);
    n->nodeType = PNT_TERNARY_OP;
    n->children.push_back(expr);
    n->children.push_back(if_true);
    n->children.push_back(if_false);
    return n;
  }

  Node * createFunctionParametersListNode(Token & t, vector<Token *> & params_tokens,
    vector<Node *> & params, vector<Node *> & default_values)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_FUNCTION_PARAMETERS_LIST;

    for (size_t i = 0; i < params.size(); i++)
    {
      Node * param = new Node(ctx, *params_tokens[i]);
      param->nodeType = PNT_FUNCTION_PARAMETER;
      param->children.push_back(params[i]);
      if (default_values[i])
        param->children.push_back(default_values[i]);
      n->children.push_back(param);
    }

    return n;
  }

  Node * createLocalFunctionNode(Token & t, Node * optional_name, Node * parameters_list, Node * function_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_LOCAL_FUNCTION;
    n->children.push_back(optional_name);
    n->children.push_back(parameters_list);
    n->children.push_back(function_body);
    return n;
  }

  Node * createClassMethodNode(Token & t, Node * name, Node * parameters_list, Node * function_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_CLASS_METHOD;
    n->children.push_back(name);
    n->children.push_back(parameters_list);
    n->children.push_back(function_body);
    return n;
  }

  Node * createClassConstructorNode(Token & t, Node * parameters_list, Node * function_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_CLASS_CONSTRUCTOR;
    n->children.push_back(nullptr);
    n->children.push_back(parameters_list);
    n->children.push_back(function_body);
    return n;
  }

  Node * createAccessConstructorNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_ACCESS_CONSTRUCTOR;
    return n;
  }

  Node * createBaseNode(Token & t)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_BASE;
    return n;
  }

  Node * createParenNode(Token & t, Node * expression)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_EXPRESSION_PAREN;
    n->children.push_back(expression);
    return n;
  }

  Node * createMakeKeyNode(Token & t, Node * expression)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_MAKE_KEY;
    n->children.push_back(expression);
    return n;
  }

  Node * createFunctionNode(Token & t, Node * optional_name, Node * parameters_list, Node * function_body)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_FUNCTION;
    n->children.push_back(optional_name);
    n->children.push_back(parameters_list);
    n->children.push_back(function_body);
    return n;
  }

  Node * createLambdaNode(Token & t, Node * optional_name, Node * parameters_list, Node * lambda_expression)
  {
    Node * n = new Node(ctx, t);
    n->nodeType = PNT_LAMBDA;
    n->children.push_back(optional_name);
    n->children.push_back(parameters_list);
    n->children.push_back(lambda_expression);
    return n;
  }


  Node * parseArrayCreation()
  {
    EXPRESSION_CONTEXT_SCOPE(EC_USUAL);

    Token & opToken = *tok;
    std::vector<Node *> values;
    if (accept(TK_RSQUARE))
      return createArrayCreationNode(opToken, values);

    Token * delimiterComma = nullptr;
    Token * delimiterSpace = nullptr;

    for (;;)
    {
      Node * value = parseTernaryOp();
      if (!value)
        break;

      values.push_back(value);

      if (forwardToken(0) == TK_COMMA)
        delimiterComma = delimiterComma ? delimiterComma : &tokens[pos - 1];
      else if (forwardToken(0) != TK_RSQUARE)
        delimiterSpace = delimiterSpace ? delimiterSpace : &tokens[pos - 1];

      accept(TK_COMMA); // optional comma
      if (accept(TK_RSQUARE))
      {
        if (delimiterComma && delimiterSpace)
          ctx.warning("mixed-separators", *(delimiterComma > delimiterSpace ? delimiterComma : delimiterSpace),
            "elements of array");

        return createArrayCreationNode(opToken, values);
      }
    }

    return nullptr;
  }

  Node * parseTableCreation()
  {
    EXPRESSION_CONTEXT_SCOPE(EC_USUAL);

    Token & opToken = *tok;
    std::vector<Node *> keys;
    std::vector<Node *> values;
    std::vector<Token *> assignmentTokens;

    if (accept(TK_RBRACE))
      return createTableCreationNode(opToken, keys, values, assignmentTokens);

    for (;;)
    {
      Node * key = nullptr;
      Node * value = nullptr;

      if (accept(TK_IDENTIFIER))
      {
        key = createIdentifierNode(*tok);
        if (!accept(TK_ASSIGN))
          value = createIdentifierNode(*tok);
      }
      else if (accept(TK_LSQUARE))
      {
        key = createMakeKeyNode(*tok, parseTernaryOp());
        expect(TK_RSQUARE);
        expect(TK_ASSIGN);
      }
      else if (accept(TK_STRING_LITERAL))
      {
        key = createOperandNode(*tok);
        expect(TK_COLON);
      }
      else if (accept(TK_FUNCTION))
      {
        value = parseFunction(FT_FUNCTION);
        if (value)
          key = value->children[0]; // function name
      }

      if (!key || ctx.isError)
        break;

      assignmentTokens.push_back(tok);

      if (!value)
        value = parseTernaryOp();
      if (!value)
        break;

      keys.push_back(key);
      values.push_back(value);
      accept(TK_COMMA); // optional comma
      if (accept(TK_RBRACE))
        return createTableCreationNode(opToken, keys, values, assignmentTokens);
    }

    return nullptr;
  }

  Node * parseClassMember()
  {
    if (accept(TK_BASE))
      return createBaseNode(*tok);

    if (accept(TK_CONSTRUCTOR))
      return createAccessConstructorNode(*tok);

    if (expect(TK_IDENTIFIER))
      return createIdentifierNode(*tok);

    return nullptr;
  }

  Node * tryParseNamespaceIdentifier()
  {
    if (accept(TK_CONSTRUCTOR))
      return createAccessConstructorNode(*tok);
    else if (accept(TK_IDENTIFIER))
      return createIdentifierNode(*tok);
    else
      return nullptr;
  }

  Node * parseDeref()
  {
    Node * res = nullptr;

    if (accept(TK_IDENTIFIER))
    {
      res = createIdentifierNode(*tok);
    }
    else if (accept(TK_STRING_LITERAL) || accept(TK_INTEGER) || accept(TK_FLOAT) ||
      accept(TK_FALSE) || accept(TK_TRUE) || accept(TK_NULL))
    {
      res = createOperandNode(*tok);
    }
    else if (accept(TK_DOUBLE_COLON))
    {
      res = createRootNode(*tok);
      if (!expect(TK_IDENTIFIER))
        return nullptr;
      Node * ident = createIdentifierNode(*tok);
      res = createAccessMemberNode(res->tok, res, ident);
    }
    else if (accept(TK_THIS))
    {
      res = createThisNode(*tok);
    }
    else if (accept(TK_CONSTRUCTOR))
    {
      res = createAccessConstructorNode(*tok);
    }
    else if (accept(TK_BASE))
    {
      res = createBaseNode(*tok);
    }
    else if (accept(TK_LPAREN))
    {
      Token & tk = *tok;
      Node * expression = (expressionContext.back() == EC_CONDITION) ? parseInexprLocal() : parseTernaryOp();
      res = createParenNode(tk, expression);
      expect(TK_RPAREN);
    }
    else if (accept(TK_LSQUARE))
    {
      res = parseArrayCreation();
      if (!res)
        ctx.error(118, "expected ']' after array creation", tokens[pos].line, tokens[pos].column);
    }
    else if (accept(TK_LBRACE))
    {
      res = parseTableCreation();
      if (!res)
        ctx.error(119, "expected '}' after table creation", tokens[pos].line, tokens[pos].column);
    }
    else if (accept(TK_CLASS))
    {
      res = parseClass(tok, false, false);
    }
    else if (accept(TK_AT))
    {
      res = parseFunction(FT_LAMBDA);
    }
    else if (accept(TK_FUNCTION))
    {
      res = parseFunction(FT_FUNCTION);
    }
    else
    {
      return nullptr;
    }

    while (!ctx.isError)
    {
      if (accept(TK_DOT))
      {
        Token & opToken = *tok;
        Node * ident = parseClassMember();
        res = createAccessMemberNode(opToken, res, ident);
      }
      else if (accept(TK_NULLGETSTR))
      {
        Token & opToken = *tok;
        Node * ident = parseClassMember();
        res = createAccessMemberIfNotNullNode(opToken, res, ident);
      }
      else if (accept(TK_LSQUARE))
      {
        if (prevToken().nextEol)
          ctx.error(127, "'[' on a new line parsed as access to member of array, expected ','", tok->line, tok->column);

        Token & opToken = *tok;
        Node * expression = parseTernaryOp();
        expect(TK_RSQUARE);
        res = createAccessMemberNode(opToken, res, expression);
      }
      else if (accept(TK_NULLGETOBJ))
      {
        Token & opToken = *tok;
        Node * expression = parseTernaryOp();
        expect(TK_RSQUARE);
        res = createAccessMemberIfNotNullNode(opToken, res, expression);
      }
      else if (accept(TK_LPAREN) || accept(TK_NULLCALL))
      {
        if (prevToken().nextEol && tok->type == TK_LPAREN)
          ctx.warning("paren-is-function-call", *tok);

        Token & opToken = *tok;
        std::vector<Node *> params;

        if (accept(TK_RPAREN))
        {
          res = (opToken.type == TK_NULLCALL) ?
            createCallIfNotNullNode(opToken, res, params) :
            createCallNode(opToken, res, params);
        }
        else
        {
          Token * delimiterComma = nullptr;
          Token * delimiterSpace = nullptr;

          for (;;)
          {
            Node * param = parseTernaryOp();
            if (!param)
              break;

            params.push_back(param);

            if (ALLOW_FUNCTION_PARAMS_WITHOUT_COMMA)
            {
              if (forwardToken(0) == TK_RPAREN)
                break;

              if (forwardToken(0) == TK_COMMA)
                delimiterComma = delimiterComma ? delimiterComma : &tokens[pos - 1];
              else
                delimiterSpace = delimiterSpace ? delimiterSpace : &tokens[pos - 1];

              accept(TK_COMMA);
            }
            else if (!accept(TK_COMMA))
            {
              break;
            }
          }

          if (!expect(TK_RPAREN))
            break;

          if (delimiterComma && delimiterSpace)
            ctx.warning("mixed-separators", *(delimiterComma > delimiterSpace ? delimiterComma : delimiterSpace),
              "parameters of the function");

          res = (opToken.type == TK_LPAREN) ? createCallNode(opToken, res, params) : createCallIfNotNullNode(opToken, res, params);
        }
      }
      else
        break;
    }

    return res;
  }

  Node * parseOperand()
  {
    if (Node * deref = parseDeref())
    {
      return deref;
    }
    else
    {
      ctx.error(120, (string("expected expression but '") + token_strings[tokens[pos].type] + "' found").c_str(),
        tokens[pos].line, tokens[pos].column);
      return nullptr;
    }
  }

  Node * parseUnaryPostOp()
  {
    Node * operand = parseOperand();
    if (operand && !isEndOfStatement() && (accept(TK_PLUSPLUS) || accept(TK_MINUSMINUS)))
    {
      Token & opToken = *tok;
      return createUnaryPostOpNode(opToken, operand);
    }
    else
      return operand;
  }

  Node * parseUnaryOp()
  {
    if (accept(TK_MINUS) || accept(TK_PLUS) || accept(TK_INV) || accept(TK_NOT) || accept(TK_PLUSPLUS) || accept(TK_MINUSMINUS) ||
      accept(TK_TYPEOF) || accept(TK_DELETE) || accept(TK_CLONE))
    {
      Token & opToken = *tok;
      return createUnaryPreOpNode(opToken, parseUnaryOp());
    }
    else
    {
      return parseReaderMacro();
    }
  }

  Node * parseReaderMacro()
  {
    if (accept(TK_READER_MACRO))
    {
      Token & opToken = *tok;
      return createReaderMacroOpNode(opToken, parseOperand());
    }
    else
    {
      return parseUnaryPostOp();
    }
  }


#define DECL_PARSE_BIN_OP_FUNCTION(fn_name, accept_expression, next_function, single_op) \
  Node * fn_name() \
  { \
    std::vector<Node *> nodes; \
    std::vector<Token *> opTokens; \
    while (Node * n = next_function()) \
      if (accept_expression) \
      { \
        if (single_op && nodes.size() > 0) \
        { \
          ctx.error(116, "expected end of expression", tok->line, tok->column); \
          break; \
        } \
        opTokens.push_back(tok); \
        nodes.push_back(n); \
      } \
      else \
      { \
        nodes.push_back(n); \
        break; \
      } \
   \
    if (nodes.empty()) \
      return nullptr; \
   \
    if (nodes.size() == 1) \
      return nodes[0]; \
   \
    Node * res = nodes[0]; \
    for (int i = 1; i < int(nodes.size()); i++) \
      res = createBinaryOpNode(*opTokens[i - 1], res, nodes[i]); \
   \
    return res; \
  }




  DECL_PARSE_BIN_OP_FUNCTION(parseFactor, accept(TK_MUL) || accept(TK_DIV) || accept(TK_MODULO), parseUnaryOp, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseSum, accept(TK_PLUS) || accept(TK_MINUS), parseFactor, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseShift, accept(TK_SHIFTL) || accept(TK_SHIFTR) || accept(TK_USHIFTR), parseSum, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseLsGt,
    accept(TK_LS) || accept(TK_GT) || accept(TK_LE) || accept(TK_GE) ||
    accept(TK_IN) || accept(TK_NOTIN) || accept(TK_INSTANCEOF),
    parseShift, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseEq, accept(TK_EQ) || accept(TK_NE) || accept(TK_3WAYSCMP), parseLsGt, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseBitAnd, accept(TK_BITAND) || false, parseEq, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseBitXor, accept(TK_BITXOR) || false, parseBitAnd, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseBitOr, accept(TK_BITOR) || false, parseBitXor, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseAnd, accept(TK_AND) || false, parseBitOr, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseOr, accept(TK_OR) || false, parseAnd, false);
  DECL_PARSE_BIN_OP_FUNCTION(parseNullCoalesce, accept(TK_NULLCOALESCE) || false, parseOr, false);

  Node * parseTernaryOp()
  {
    Node * expr = parseNullCoalesce();
    if (!expr)
      return nullptr;

    if (!accept(TK_QMARK))
      return expr;

    Token & qmarkToken = *tok;

    Node * ifTrue = parseTernaryOp();
    if (!ifTrue)
    {
      ctx.error(121, (string("expected expression but '") + token_strings[tokens[pos].type] + "' found").c_str(),
        tokens[pos].line, tokens[pos].column);
      return nullptr;
    }

    if (!expect(TK_COLON))
    {
      ctx.error(122, (string("expected ':' but '") + token_strings[tokens[pos].type] + "' found").c_str(),
        tokens[pos].line, tokens[pos].column);
      return nullptr;
    }

    Node * ifFalse = parseTernaryOp();
    if (!ifFalse)
    {
      ctx.error(123, (string("expected expression but '") + token_strings[tokens[pos].type] + "' found").c_str(),
        tokens[pos].line, tokens[pos].column);
      return nullptr;
    }

    Node * res = createTernaryOpNode(qmarkToken, expr, ifTrue, ifFalse);
    return res;
  }


  DECL_PARSE_BIN_OP_FUNCTION(parseAssignExpression,
    accept(TK_ASSIGN) || accept(TK_PLUSEQ) || accept(TK_MINUSEQ) || accept(TK_MULEQ) || accept(TK_DIVEQ) ||
      accept(TK_MODEQ) || accept(TK_NEWSLOT),
    parseTernaryOp, true);


  DECL_PARSE_BIN_OP_FUNCTION(parseInexprAssignExpression,
    accept(TK_INEXPR_ASSIGNMENT),
    parseTernaryOp, true);


  Node * parseInexprLocal()
  {
    if (accept(TK_LOCAL))
    {
      Token & tk = *tok;
      expect(TK_IDENTIFIER);
      Node * key = createIdentifierNode(*tok);
      expect(TK_INEXPR_ASSIGNMENT);
      Node * value = parseTernaryOp();
      return createInexprVarDeclaratorNode(tk, key, value);
    }

    return parseInexprAssignExpression();
  }


  bool isEndOfStatement()
  {
    return tok->nextEol || forwardToken(0) == TK_SEMICOLON || forwardToken(0) == TK_RBRACE;
  }


  void parseListOfVars(Node * out_list, NodeType element_node_type)
  {
    while (out_list->children.empty() ? expect(TK_IDENTIFIER) : accept(TK_IDENTIFIER))
    {
      Node * decl = new Node(ctx, *tok);
      decl->nodeType = element_node_type;
      decl->children.push_back(createIdentifierNode(*tok));
      if (accept(TK_ASSIGN))
        decl->children.push_back(parseTernaryOp());

      out_list->children.push_back(decl);

      if (forwardToken(0) != TK_RBRACE && forwardToken(0) != TK_RSQUARE)
        expect(TK_COMMA);
    }
  }

  void checkBraceIdentationStyle()
  {
    if (pos > 0 && forwardToken(0) == TK_LBRACE && tokens[pos - 1].nextEol)
      ctx.warning("egyptian-braces", tokens[pos]);
  }

  Node * parseLocalVarDeclaration()
  {
    Token * tk = tok; // = "local"
    std::vector<Node *> varKeys;
    std::vector<Node *> varValues;
    while (!ctx.isError)
    {
      if (accept(TK_LBRACE))
      {
        Node * list = new Node(ctx, *tok);
        list->nodeType = PNT_LIST_OF_KEYS_TABLE;
        parseListOfVars(list, PNT_VAR_DECLARATOR);
        varKeys.push_back(list);
        expect(TK_RBRACE);
      }
      else if (accept(TK_LSQUARE))
      {
        Node * list = new Node(ctx, *tok);
        list->nodeType = PNT_LIST_OF_KEYS_ARRAY;
        parseListOfVars(list, PNT_VAR_DECLARATOR);
        varKeys.push_back(list);
        expect(TK_RSQUARE);
      }
      else if (expect(TK_IDENTIFIER))
      {
        varKeys.push_back(createIdentifierNode(*tok));
      }

      if (ctx.isError)
        break;

      if (accept(TK_ASSIGN))
      {
        varValues.push_back(parseTernaryOp());
        if (!isEndOfStatement())
          expect(TK_COMMA);
      }
      else if (accept(TK_COMMA) || isEndOfStatement())
      {
        varValues.push_back(nullptr);
      }
      else
      {
        varValues.push_back(nullptr);
        break;
      }

      if (tok->type != TK_COMMA && isEndOfStatement())
        break;
    }

    if (varKeys.empty())
    {
      ctx.error(124, "expected name of variable", tok->line, tok->column);
      return nullptr;
    }
    return ctx.isError ? nullptr : createLocalVarDeclarationNode(*tk, varKeys, varValues);
  }

  enum FunctionType
  {
    FT_FUNCTION,
    FT_LOCAL_FUNCTION,
    FT_LAMBDA,
    FT_CLASS_METHOD,
    FT_CLASS_CONSTRUCTOR,
  };

  Node * parseFunction(FunctionType function_type)
  {
    EXPRESSION_CONTEXT_SCOPE(EC_USUAL);

    Token * tk = tok;
    Node * functionName = nullptr;

    switch (function_type)
    {
    case FT_FUNCTION:
      if (forwardToken(0) == TK_IDENTIFIER)
        functionName = tryParseNamespaceIdentifier();
      break;

    case FT_LAMBDA:
      if (accept(TK_IDENTIFIER))
        functionName = createIdentifierNode(*tok);
      break;

    case FT_LOCAL_FUNCTION:
    case FT_CLASS_METHOD:
      expect(TK_IDENTIFIER);
      functionName = createIdentifierNode(*tok);
      break;

    case FT_CLASS_CONSTRUCTOR:
      break;
    }


    expect(TK_LPAREN);
    Token * lparenTok = tok;
    vector<Token *> paramTok;
    vector<Node *> paramNames;
    vector<Node *> defaultValues;

    if (!accept(TK_RPAREN))
      while (!ctx.isError)
      {
        if (accept(TK_VARPARAMS))
        {
          paramTok.push_back(tok);
          paramNames.push_back(createVarParamsNode(*tok));
          defaultValues.push_back(nullptr);
          expect(TK_RPAREN);
          break;
        }

        if (accept(TK_LBRACE))
        {
          paramTok.push_back(tok);
          Node * list = new Node(ctx, *tok);
          list->nodeType = PNT_LIST_OF_KEYS_TABLE;
          parseListOfVars(list, PNT_FUNCTION_PARAMETER);
          paramNames.push_back(list);
          expect(TK_RBRACE);

          defaultValues.push_back(nullptr);
        }
        else if (accept(TK_LSQUARE))
        {
          paramTok.push_back(tok);
          Node * list = new Node(ctx, *tok);
          list->nodeType = PNT_LIST_OF_KEYS_ARRAY;
          parseListOfVars(list, PNT_FUNCTION_PARAMETER);
          paramNames.push_back(list);
          expect(TK_RSQUARE);

          defaultValues.push_back(nullptr);
        }
        else if (expect(TK_IDENTIFIER))
        {
          paramTok.push_back(tok);
          paramNames.push_back(createIdentifierNode(*tok));
          if (accept(TK_ASSIGN))
            defaultValues.push_back(parseTernaryOp());
          else
            defaultValues.push_back(nullptr);
        }

        if (accept(TK_RPAREN))
          break;

        if (!expect(TK_COMMA))
          break;
      }

    Node * parametersList = createFunctionParametersListNode(*lparenTok, paramTok, paramNames, defaultValues);


    Node * functionBody = nullptr;

    if (function_type == FT_LAMBDA)
    {
      if (ALLOW_ASSIGNMENT_IN_LAMBDA)
        functionBody = parseAssignExpression();
      else
        functionBody = parseTernaryOp();
    }
    else
    {
      if (forwardToken(0) != TK_LBRACE)
      {
        ctx.warning("single-statement-function", *tok);
        functionBody = parseStatementList(*tok, 1, false, true);
      }
      else
      {
        checkBraceIdentationStyle();
        expect(TK_LBRACE);
        functionBody = parseStatementList(*tok, 1, false, false);
        expect(TK_RBRACE);
      }
    }

    switch (function_type)
    {
    case FT_FUNCTION:
      return createFunctionNode(*tk, functionName, parametersList, functionBody);
    case FT_LOCAL_FUNCTION:
      return createLocalFunctionNode(*tk, functionName, parametersList, functionBody);
    case FT_CLASS_METHOD:
      return createClassMethodNode(*tk, functionName, parametersList, functionBody);
    case FT_CLASS_CONSTRUCTOR:
      return createClassConstructorNode(*tk, parametersList, functionBody);
    case FT_LAMBDA:
      return createLambdaNode(*tk, functionName, parametersList, functionBody);
    }

    return nullptr;
  }


  Node * parseClass(Token * class_token, bool expect_class_name, bool is_local)
  {
    EXPRESSION_CONTEXT_SCOPE(EC_USUAL);

    Node * className = nullptr;
    Node * extends = nullptr;
    vector<Node *> classMembers;
    if (expect_class_name)
      className = parseDeref();

    if (accept(TK_EXTENDS))
      extends = parseTernaryOp();

    checkBraceIdentationStyle();
    expect(TK_LBRACE);

    while (!ctx.isError)
    {
      if (accept(TK_RBRACE))
        break;

      if (accept(TK_SEMICOLON))
        continue;

      bool isStatic = accept(TK_STATIC);

      if (!isStatic && accept(TK_CONSTRUCTOR))
      {
        Token * memberTok = tok;
        Node * memberValue = parseFunction(FT_CLASS_CONSTRUCTOR);
        Node * memberName = nullptr;

        Node * member = new Node(ctx, *memberTok);
        member->nodeType = PNT_CLASS_MEMBER;
        member->children.push_back(memberName);
        member->children.push_back(memberValue);
        classMembers.push_back(member);
      }
      else if (accept(TK_FUNCTION))
      {
        Token * memberTok = tok;
        Node * memberValue = parseFunction(FT_CLASS_METHOD);
        Node * memberName = memberValue ? memberValue->children[0] : nullptr;

        Node * member = new Node(ctx, *memberTok);
        member->nodeType = isStatic ? PNT_STATIC_CLASS_MEMBER : PNT_CLASS_MEMBER;
        member->children.push_back(memberName);
        member->children.push_back(memberValue);
        classMembers.push_back(member);
      }
      else if (accept(TK_LSQUARE))
      {
        Node * memberName = createMakeKeyNode(*tok, parseTernaryOp());
        expect(TK_RSQUARE);
        expect(TK_ASSIGN);
        Token * memberTok = tok;
        Node * memberValue = parseTernaryOp();

        Node * member = new Node(ctx, *memberTok);
        member->nodeType = isStatic ? PNT_STATIC_CLASS_MEMBER : PNT_CLASS_MEMBER;
        member->children.push_back(memberName);
        member->children.push_back(memberValue);
        classMembers.push_back(member);
      }
      else if (expect(TK_IDENTIFIER))
      {
        Node * memberName = createIdentifierNode(*tok);
        expect(TK_ASSIGN);
        Token * memberTok = tok;
        Node * memberValue = parseTernaryOp();

        Node * member = new Node(ctx, *memberTok);
        member->nodeType = isStatic ? PNT_STATIC_CLASS_MEMBER : PNT_CLASS_MEMBER;
        member->children.push_back(memberName);
        member->children.push_back(memberValue);
        classMembers.push_back(member);
      }
    }

    Node * res = new Node(ctx, *class_token);
    res->nodeType = is_local ? PNT_LOCAL_CLASS : PNT_CLASS;
    res->children.push_back(className);
    res->children.push_back(extends);
    res->children.push_back(nullptr); // attributes (removed code)
    for (size_t i = 0; i < classMembers.size(); i++)
      res->children.push_back(classMembers[i]);
    return res;
  }

  Node * parseEnumStatement(Token * enum_token, bool is_global)
  {
    Node * enumName = nullptr;
    Node * extends = nullptr;
    vector<Node *> enumMembers;
    expect(TK_IDENTIFIER);
    enumName = createIdentifierNode(*tok);

    checkBraceIdentationStyle();
    expect(TK_LBRACE);

    while (!ctx.isError)
    {
      if (accept(TK_RBRACE))
        break;

      if (expect(TK_IDENTIFIER))
      {
        Node * memberName = createIdentifierNode(*tok);
        Token * memberTok = tok;
        Node * memberValue = nullptr;

        if (accept(TK_ASSIGN))
          memberValue = parseTernaryOp();

        Node * member = new Node(ctx, *memberTok);
        member->nodeType = PNT_ENUM_MEMBER;
        member->children.push_back(memberName);
        if (memberValue)
          member->children.push_back(memberValue);
        enumMembers.push_back(member);
      }

      accept(TK_COMMA);
    }

    Node * res = new Node(ctx, *enum_token);
    res->nodeType = is_global ? PNT_GLOBAL_ENUM : PNT_ENUM;
    res->children.push_back(enumName);
    for (size_t i = 0; i < enumMembers.size(); i++)
      res->children.push_back(enumMembers[i]);
    return res;
  }


  Node * parseConstStatement(Token * const_token, bool is_global)
  {
    expect(TK_IDENTIFIER);
    Node * name = createIdentifierNode(*tok);
    expect(TK_ASSIGN);
    Node * value = parseTernaryOp();

#define ACCEPT_ONLY_SCALAR_CONST 1
#if (ACCEPT_ONLY_SCALAR_CONST)
    Node * check = value;
    if (check->nodeType == PNT_UNARY_PRE_OP && check->tok.type == TK_MINUS && check->children.size() == 1 &&
      (check->children[0]->nodeType == PNT_FLOAT || check->children[0]->nodeType == PNT_INTEGER))
    {
      check = value->children[0];
    }

    if (check && check->nodeType != PNT_INTEGER && check->nodeType != PNT_BOOL && check->nodeType != PNT_FLOAT &&
      check->nodeType != PNT_STRING)
    {
      ctx.error(130, "expected scalar (boolean, integer, float, string)", check->tok.line, check->tok.column);
    }

#endif

    return createConstDeclarationNode(*const_token, name, value, is_global);
  }


  Node * parseStatement(bool expect_statement_delimiter)
  {
    if (forwardToken(0) == TK_EOF)
      return nullptr;

    if (expect_statement_delimiter)
      if (accept(TK_SEMICOLON))
        return createEmptyStatementNode(*tok);

    Node * res = nullptr;
    if (accept(TK_LOCAL))
    {
      if (accept(TK_CLASS))
        res = parseClass(tok, true, true);
      else if (accept(TK_FUNCTION))
        res = parseFunction(FT_LOCAL_FUNCTION);
      else
        res = parseLocalVarDeclaration();
    }
    else if (accept(TK_CONST))
    {
      res = parseConstStatement(tok, false);
    }
    else if (accept(TK_LBRACE))
    {
      res = parseStatementList(*tok, 1, false, false);
      expect(TK_RBRACE);
    }
    else if (accept(TK_RETURN))
    {
      Token * tk = tok;
      Node * functionResult = nullptr;
      if (!isEndOfStatement())
        functionResult = parseTernaryOp();
      res = createReturnNode(*tk, functionResult);
    }
    else if (accept(TK_YIELD))
    {
      Token * tk = tok;
      Node * functionResult = nullptr;
      if (!isEndOfStatement())
        functionResult = parseTernaryOp();
      res = createYieldNode(*tk, functionResult);
    }
    else if (accept(TK_BREAK))
    {
      res = createBreakNode(*tok);
    }
    else if (accept(TK_CONTINUE))
    {
      res = createContinueNode(*tok);
    }
    else if (accept(TK_THROW))
    {
      Token * tk = tok;
      Node * expression = parseTernaryOp();
      res = createThrowNode(*tok, expression);
    }
    else if (accept(TK_TRY))
    {
      Token * tk = tok;
      checkBraceIdentationStyle();
      Node * tryBody = parseStatement(false);
      expect(TK_CATCH);
      expect(TK_LPAREN);
      expect(TK_IDENTIFIER);
      Node * id = createIdentifierNode(*tok);
      expect(TK_RPAREN);
      checkBraceIdentationStyle();
      Node * catchBody = parseStatement(true);
      res = createTryCatchNode(*tok, tryBody, id, catchBody);
    }
    else if (accept(TK_IF))
    {
      Token * prevElse = (pos >= 2 && forwardToken(-2) == TK_ELSE && tok->line == tokens[pos - 2].line) ?
        &(tokens[pos - 2]) : nullptr;
      if (prevElse && prevElse->type == TK_ELSE && pos >= 3)
        if (forwardToken(-3) == TK_RBRACE && tok->line == tokens[pos - 3].line)
          prevElse = &(tokens[pos - 3]);

      Token * baseTok = prevElse ? prevElse : tok;

      Token * tk = tok;
      expect(TK_LPAREN);
      expressionContext.push_back(EC_CONDITION);
      Node * expression = parseInexprLocal();
      expressionContext.pop_back();
      expect(TK_RPAREN);
      checkBraceIdentationStyle();
      Node * ifTrue = parseStatement(true);
      if (forwardToken(0) != TK_ELSE && !isEndOfStatement())
        ctx.warning("statement-on-same-line", *tok, "then");

      Node * ifFalse = nullptr;
      if (accept(TK_ELSE))
      {
        Token * secondTok = (forwardToken(-2) == TK_RBRACE && tok->line == tokens[pos - 2].line) ?
          &(tokens[pos - 2]) : tok;

        if (secondTok->line != baseTok->line && secondTok->column != baseTok->column)
        {
          ctx.warning("suspicious-formatting", *tok,
            std::to_string(tk->line).c_str(), std::to_string(tok->line).c_str());
        }

        checkBraceIdentationStyle();
        ifFalse = parseStatement(true);
      }

      if (ifFalse)
        if (forwardToken(0) != TK_ELSE && !isEndOfStatement())
          ctx.warning("statement-on-same-line", *tok, "else");

      if (forwardToken(0) != TK_EOF && forwardToken(0) != TK_RBRACE && forwardToken(0) != TK_RSQUARE &&
        forwardToken(0) != TK_RPAREN && forwardToken(0) != TK_COMMA)
      {
        Token * lastIfTok = &(tokens[pos - 1]);
        if (tokens[pos].line != lastIfTok->line && tokens[pos].column > baseTok->column)
        {
          ctx.warning("suspicious-formatting", tokens[pos],
            std::to_string(tk->line).c_str(), std::to_string(tokens[pos].line).c_str());
        }
      }

      res = createIfElseNode(*tk, expression, ifTrue, ifFalse);
    }
    else if (accept(TK_WHILE))
    {
      Token * tk = tok;
      expect(TK_LPAREN);
      expressionContext.push_back(EC_CONDITION);
      Node * expression = parseInexprLocal();
      expressionContext.pop_back();
      expect(TK_RPAREN);
      checkBraceIdentationStyle();
      Node * loopBody = parseStatement(true);

      if (loopBody && loopBody->nodeType != PNT_STATEMENT_LIST && !isEndOfStatement())
        ctx.warning("statement-on-same-line", *tok, "loop body");

      if (forwardToken(0) != TK_EOF && forwardToken(0) != TK_RBRACE)
      {
        Token * lastIfTok = &(tokens[pos - 1]);
        if (tokens[pos].line != lastIfTok->line && tokens[pos].column > tk->column)
        {
          ctx.warning("suspicious-formatting", tokens[pos],
            std::to_string(tk->line).c_str(), std::to_string(tokens[pos].line).c_str());
        }
      }

      res = createWhileLoopNode(*tk, expression, loopBody);
    }
    else if (accept(TK_DO))
    {
      Token * tk = tok;
      checkBraceIdentationStyle();
      Node * loopBody = parseStatement(false);
      expect(TK_WHILE);
      expect(TK_LPAREN);
      Node * expression = parseTernaryOp();
      expect(TK_RPAREN);
      res = createDoWhileLoopNode(*tk, expression, loopBody);
    }
    else if (accept(TK_FOR))
    {
      Token * tk = tok;
      expect(TK_LPAREN);

      Node * initialization = nullptr;
      Node * expression = nullptr;
      Node * increment = nullptr;

      if (!accept(TK_SEMICOLON))
      {
        if (accept(TK_LOCAL))
          initialization = parseLocalVarDeclaration();
        else
          initialization = parseAssignExpression();
        expect(TK_SEMICOLON);
      }

      if (!accept(TK_SEMICOLON))
      {
        expressionContext.push_back(EC_CONDITION);
        expression = parseInexprLocal();
        expressionContext.pop_back();
        expect(TK_SEMICOLON);
      }

      if (!accept(TK_RPAREN))
      {
        increment = parseAssignExpression();
        expect(TK_RPAREN);
      }

      checkBraceIdentationStyle();
      Node * loopBody = parseStatement(true);

      if (loopBody && loopBody->nodeType != PNT_STATEMENT_LIST && !isEndOfStatement())
        ctx.warning("statement-on-same-line", *tok, "loop body");

      if (forwardToken(0) != TK_EOF && forwardToken(0) != TK_RBRACE)
      {
        Token * lastIfTok = &(tokens[pos - 1]);
        if (tokens[pos].line != lastIfTok->line && tokens[pos].column > tk->column)
        {
          ctx.warning("suspicious-formatting", tokens[pos],
            std::to_string(tk->line).c_str(), std::to_string(tokens[pos].line).c_str());
        }
      }

      res = createForLoopNode(*tk, initialization, expression, increment, loopBody);
    }
    else if (accept(TK_FOREACH))
    {
      Token * tk = tok;
      expect(TK_LPAREN);

      Node * variable = nullptr;
      Node * index = nullptr;
      Node * container = nullptr;

      if (expect(TK_IDENTIFIER))
      {
        variable = createIdentifierNode(*tok);
        if (accept(TK_COMMA))
          if (expect(TK_IDENTIFIER))
            index = createIdentifierNode(*tok);

        expect(TK_IN);
        container = parseTernaryOp();
        expect(TK_RPAREN);
      }

      checkBraceIdentationStyle();
      Node * loopBody = parseStatement(true);

      if (loopBody && loopBody->nodeType != PNT_STATEMENT_LIST && !isEndOfStatement())
        ctx.warning("statement-on-same-line", *tok, "loop body");

      if (forwardToken(0) != TK_EOF && forwardToken(0) != TK_RBRACE)
      {
        Token * lastIfTok = &(tokens[pos - 1]);
        if (tokens[pos].line != lastIfTok->line && tokens[pos].column > tk->column)
        {
          ctx.warning("suspicious-formatting", tokens[pos],
            std::to_string(tk->line).c_str(), std::to_string(tokens[pos].line).c_str());
        }
      }

      res = createForEachLoopNode(*tk, variable, index, container, loopBody);
    }
    else if (accept(TK_FUNCTION))
    {
      res = parseFunction(FT_FUNCTION);
    }
    else if (accept(TK_CLASS))
    {
      res = parseClass(tok, true, false);
    }
    else if (accept(TK_ENUM))
    {
      res = parseEnumStatement(tok, false);
    }
    else if (accept(TK_SWITCH))
    {
      Token * tk = tok;
      expect(TK_LPAREN);
      Node * expression = parseTernaryOp();
      expect(TK_RPAREN);
      checkBraceIdentationStyle();
      expect(TK_LBRACE);

      bool defaultPresent = false;
      vector<Token *> caseTestsTokens;
      vector<Node *> caseTests;
      vector<Node *> statements;

      while (!ctx.isError)
      {
        if (accept(TK_RBRACE))
          break;

        Node * test = nullptr;
        Token * caseTok = &emptyToken;
        if (accept(TK_DEFAULT))
        {
          if (defaultPresent)
            ctx.error(125, "multiple default clauses", tok->line, tok->column);

          defaultPresent = true;
          caseTok = tok;
          expect(TK_COLON);
        }
        else
        {
          expect(TK_CASE);
          caseTok = tok;
          test = parseTernaryOp();
          expect(TK_COLON);
        }

        checkBraceIdentationStyle();
        Node * caseBody = parseStatementList(*tok, 1, true, false);
        caseTestsTokens.push_back(caseTok);
        caseTests.push_back(test);
        statements.push_back(caseBody);
      }

      res = createSwitchNode(*tk, expression, caseTestsTokens, caseTests, statements);
    }
    else if (accept(TK_GLOBAL))
    {
      if (accept(TK_CONST))
        res = parseConstStatement(tok, true);
      else if (accept(TK_ENUM))
        res = parseEnumStatement(tok, true);
      else
        ctx.error(129, "global can be applied to const or enum only", tok->line, tok->column);
    }
    else if (accept(TK_DOCSTRING))
    {
      res = createDocStringNode(*tok);
    }
    else
    {
      res = parseAssignExpression();
    }


    if (expect_statement_delimiter)
    {
      if (!isEndOfStatement() && tok->type != TK_RBRACE && tok->type != TK_SEMICOLON)
        ctx.error(126, "expected end of statement (; or lf)", tok->line, tok->column);

      if (tok->type != TK_RBRACE)
        accept(TK_SEMICOLON);
    }

    return res;
  }

  Node * parseStatementList(Token & statement_list_token, int depth, bool inside_switch, bool single_statement)
  {
    EXPRESSION_CONTEXT_SCOPE(EC_USUAL);
    Node * statements = new Node(ctx, statement_list_token);
    statements->nodeType = PNT_STATEMENT_LIST;
    if (depth > 0 && forwardToken(0) == TK_RBRACE)
      return statements;

    while (!ctx.isError)
    {
      if (inside_switch)
        if (forwardToken(0) == TK_CASE || forwardToken(0) == TK_DEFAULT)
          break;

      Node * statement = nullptr;
      {
        statement = parseStatement(true);
      }
      if (!statement)
        break;

      statements->children.push_back(statement);
      if (forwardToken(0) == TK_EOF || (depth > 0 && forwardToken(0) == TK_RBRACE))
        break;

      if (single_statement)
        break;
    }

    return statements;
  }
};

static Node * precess_import(Lexer & lex, Parser & parser)
{
  vector<Node *> vars;

  // HACK: add tokens after TK_EOF
  for (auto && im: lex.ctx.imports)
    for (auto && slot : im.slots)
      if (!slot.importAsIdentifier.empty())
      {
        lex.ctx.stringList.insert(slot.importAsIdentifier);
        auto listIt = lex.ctx.stringList.find(slot.importAsIdentifier);
        Token::U u;
        u.s = listIt->c_str();
        lex.tokens.push_back({ (TokenType)TK_IDENTIFIER, false, false, (unsigned short)slot.column, slot.line, u });
        vars.push_back(parser.createIdentifierNode(lex.tokens.back()));
      }

  return vars.size() ? parser.createImportVarDeclarationNode(vars) : nullptr;
}

Node * sq3_parse(Lexer & lex)
{
  emptyToken.nextEol = false;
  emptyToken.line = 1;
  emptyToken.column = 1;
  emptyToken.u.i = 0;

  Parser parser(lex);
  Node * res = parser.parseStatementList(emptyToken, 0, false, false);
  Node * imports = precess_import(lex, parser);
  if (imports)
    res->children.insert(res->children.begin(), 1, imports);

  return res;
}
