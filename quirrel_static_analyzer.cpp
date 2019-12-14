#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string>
#include <ctype.h>
#include <map>
#include <array>
#include <vector>
#include <set>
#include <algorithm>

#include <fstream>
#include <streambuf>

#include "quirrel_parser.h"
#include "module_exports.h"

using namespace std;


static bool variable_presense_check = true;

struct AnalyzerMessage
{
  int intId;
  const char * textId;
  const char * messageText;
};


struct BraceCounter
{
  int braceDepth = 0;
  int parenDepth = 0;
  int squareDepth = 0;

  bool update(TokenType token_type)
  {
    switch (token_type)
    {
    case TK_LBRACE:
      braceDepth++;
      return true;
    case TK_RBRACE:
      braceDepth--;
      return true;
    case TK_LSQUARE:
    case TK_NULLGETOBJ:
      squareDepth++;
      return true;
    case TK_RSQUARE:
      squareDepth--;
      return true;
    case TK_LPAREN:
    case TK_NULLCALL:
      parenDepth++;
      return true;
    case TK_RPAREN:
      squareDepth--;
      return true;
    default:
      return false;
    }
  }
};

string full_ident_name(const std::vector<Token> & tokens, int begin_index)
{
  string res = tokens[begin_index].u.s;
  for (int i = begin_index - 1; i >= 0; i--)
  {
    if (tokens[i].type == TK_DOT || tokens[i].type == TK_NULLGETSTR)
      res.insert(res.begin(), '.');
    else if (tokens[i].type == TK_IDENTIFIER)
      res = string(tokens[i].u.s) + res;
    else
      break;
  }
  return res;
}

bool is_arith_op_token(TokenType type)
{
  return type == TK_PLUS || type == TK_MINUS || type == TK_MODULO || type == TK_MUL || type == TK_DIV || type == TK_BITAND
    || type == TK_BITOR || type == TK_BITXOR || type == TK_PLUSPLUS || type == TK_MINUSMINUS;
}

bool is_cmp_op_token(TokenType type)
{
  return type == TK_LE || type == TK_LS || type == TK_GE || type == TK_GT || type == TK_3WAYSCMP;
}


namespace trusted
{
  enum TrustedContext
  {
    TR_PARENT_NOT_FOUND,
    TR_CHILD_NOT_FOUND,
    TR_CONST,
    TR_LOCAL,
    TR_GLOBAL,
  };

  bool trusted_identifiers;
  map<string, set<string> > trusted_consts;
  map<string, set<string> > trusted_locals;
  map<string, set<string> > trusted_globals;

  void clear()
  {
    trusted_identifiers = false;
    trusted_consts.clear();
    trusted_locals.clear();
    trusted_globals.clear();
  }

  void add(TrustedContext ident_context, const string & parent, const string & child)
  {
    map<string, set<string> > * m = nullptr;
    switch (ident_context)
    {
    case trusted::TR_CONST:
      m = &trusted_consts;
      break;
    case trusted::TR_LOCAL:
      m = &trusted_locals;
      break;
    case trusted::TR_GLOBAL:
      m = &trusted_globals;
      break;
    default:
      break;
    }

    if (!m)
      return;

    trusted_identifiers = true;

    auto it = m->find(parent);
    if (it == m->end())
    {
      set<string> s;
      if (!child.empty())
        s.insert(child);
      m->insert(make_pair(parent, s));
    }
    else
      it->second.insert(child);
  }

  TrustedContext find(const string & parent, const string & child)
  {
    {
      auto it = trusted_consts.find(parent);
      if (it != trusted_consts.end())
      {
        if (child.empty() || it->second.empty() || it->second.find(child) != it->second.end())
          return TR_CONST;
        else
          return TR_CHILD_NOT_FOUND;
      }
    }
    {
      auto it = trusted_locals.find(parent);
      if (it != trusted_locals.end())
      {
        if (child.empty() || it->second.empty() || it->second.find(child) != it->second.end())
          return TR_LOCAL;
        else
          return TR_CHILD_NOT_FOUND;
      }
    }
    {
      auto it = trusted_globals.find(parent);
      if (it != trusted_globals.end())
      {
        if (child.empty() || it->second.empty() || it->second.find(child) != it->second.end())
          return TR_GLOBAL;
        else
          return TR_CHILD_NOT_FOUND;
      }
    }
    return TR_PARENT_NOT_FOUND;
  }

};


// used in 2-pass scan
static bool two_pass_scan = false;

struct IdentTree
{
  map<string, IdentTree *> children;
  vector<string> extends; // path to class
};

IdentTree ident_root; // root
set <string> ever_declared;

vector<pair<Node *, pair<Node *, bool> > > nearest_assignments; // name { expression, is_optional }

static void collect_ever_declared(Lexer & lexer)
{
  bool res = true;
  const std::vector<Token> & tokens = lexer.tokens;
  CompilationContext & ctx = lexer.getCompilationContext();

  for (int i = 0; i < int(tokens.size()) - 1; i++)
  {
    TokenType next = tokens[i + 1].type;
    TokenType prev = (i > 0) ? tokens[i - 1].type : TK_EMPTY;
    TokenType prev2 = (i > 1) ? tokens[i - 2].type : TK_EMPTY;

    if (tokens[i].type == TK_IDENTIFIER && (next == TK_ASSIGN || next == TK_NEWSLOT ||
      prev == TK_CLASS || prev == TK_FUNCTION || prev == TK_CONST))
    {
      if (prev != TK_LOCAL && prev2 != TK_LOCAL && prev != TK_DOT && prev != TK_LPAREN && prev != TK_COMMA)
      {
        ever_declared.insert(std::string(tokens[i].u.s));
      }
    }
  }
}

static vector<string> node_to_path(Node * node)
{
  vector<string> res;

  if (node && node->nodeType == PNT_IDENTIFIER)
  {
    res.push_back(string(node->tok.u.s));
    return res;
  }

  while (node && (node->nodeType == PNT_ACCESS_MEMBER || (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_DOUBLE_COLON)))
  {
    if (node->children[1] && node->children[1]->nodeType == PNT_IDENTIFIER)
      res.insert(res.begin(), string(node->children[1]->tok.u.s));

    if (node->children[0] && node->children[0]->nodeType == PNT_IDENTIFIER)
      res.insert(res.begin(), string(node->children[0]->tok.u.s));

    node = node->children[0];
  }

  return res;
}

static void set_sub_tree_by_path(IdentTree * tree, IdentTree * subTree, vector<string> & path)
{
  if (path.size() == 0)
    return; // internal error

  for (size_t i = 0; i < path.size(); i++)
  {
    auto it = tree->children.find(path[i]);
    if (it == tree->children.end())
    {
      IdentTree * item = new IdentTree;
      tree->children.insert(make_pair(path[i], item));
      tree = item;
    }
    else
    {
      if (!it->second)
        it->second = new IdentTree;

      tree = it->second;
    }
  }

  if (subTree && tree)
  {
    tree->children.insert(subTree->children.begin(), subTree->children.end());
    if (!subTree->extends.empty())
      tree->extends = subTree->extends;
  }
}


static bool global_collect_tree(Node * node, IdentTree * tree)
{
  if (!node || !tree)
    return false;

  if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NEWSLOT)
  {
    vector<string> path = node_to_path(node->children[0]);
    IdentTree * subTree = new IdentTree;
    if (!global_collect_tree(node->children[1], subTree))
    {
      delete subTree;
      subTree = nullptr;
    }
    set_sub_tree_by_path(tree, subTree, path);
  }
  else if (node->nodeType == PNT_STATEMENT_LIST) // root
  {
    for (size_t i = 0; i < node->children.size(); i++)
    {
      Node * cur = node->children[i];
      if (!cur)
        continue;

      if ((cur->nodeType == PNT_BINARY_OP && cur->tok.type == TK_NEWSLOT) ||
        ((cur->nodeType == PNT_CLASS || cur->nodeType == PNT_LOCAL_CLASS) && cur->children[0]))
      {
        vector<string> path = node_to_path(cur->children[0]);
        IdentTree * subTree = new IdentTree;
        if (!global_collect_tree(cur->nodeType == PNT_BINARY_OP ? cur->children[1] : cur, subTree))
        {
          delete subTree;
          subTree = nullptr;
        }
        set_sub_tree_by_path(tree, subTree, path);
      }

      if (cur->nodeType == PNT_FUNCTION)
      {
        vector<string> path = node_to_path(cur->children[0]);
        set_sub_tree_by_path(tree, nullptr, path);
      }

      if (cur->nodeType == PNT_GLOBAL_ENUM)
      {
        ident_root.children.insert(make_pair(string(cur->children[0]->tok.u.s), nullptr));
      }

      if (cur->nodeType == PNT_IF_ELSE)
      {
        global_collect_tree(cur->children[1], tree);
        if (cur->children.size() > 2) // else-node
          global_collect_tree(cur->children[2], tree);
      }


      // local ClassName = class extends XXXX {}
      if (cur->nodeType == PNT_LOCAL_VAR_DECLARATION && cur->children.size() > 0 &&
        cur->children[0]->nodeType == PNT_VAR_DECLARATOR && cur->children[0]->children.size() == 2)
      {
        Node * nameNode = cur->children[0]->children[0];
        Node * classNode = cur->children[0]->children[1];
        if (nameNode && classNode && classNode->nodeType == PNT_CLASS && classNode->children[1]) // children[1] - extends
        {
          vector<string> path = node_to_path(nameNode);
          IdentTree * subTree = new IdentTree;
          global_collect_tree(classNode, subTree);
          set_sub_tree_by_path(tree, subTree, path);
        }
      }
    }
    return true;
  }

  if (node->nodeType == PNT_TABLE_CREATION || node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS)
  {
    bool isClass = (node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS);
    if (isClass && node->children[1])
      tree->extends = node_to_path(node->children[1]);

    for (size_t i = isClass ? 3 : 0; i < node->children.size(); i++)
    {
      Node * cur = node->children[i];
      if (!cur)
        continue;

      if (cur->nodeType == PNT_KEY_VALUE || cur->nodeType == PNT_CLASS_MEMBER || cur->nodeType == PNT_STATIC_CLASS_MEMBER)
        if (cur->children[0])
        {
          vector<string> path = node_to_path(cur->children[0]);
          IdentTree * subTree = new IdentTree;
          if (cur->children.size() < 2 || !global_collect_tree(cur->children[1], subTree))
          {
            delete subTree;
            subTree = nullptr;
          }
          set_sub_tree_by_path(tree, subTree, path);
        }
    }
    return true;
  }

  return false;
}



static bool is_ident_visible(const char * ident, vector<Node *> & nodePath)
{
  vector<string> path;
  vector<string> extends;

  for (size_t i = nodePath.size() - 1; i > 1; i--)
  {
    Node * node = nodePath[i];
    if (!node)
      break;

    if (node->children.size() > 0 && node->children[0])
    {
      if (((node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS) && node->children[0]) ||
        (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NEWSLOT && nodePath[i - 2] == nullptr) ||
        (node->nodeType == PNT_FUNCTION && nodePath[i - 2] == nullptr) ||
        ((node->nodeType == PNT_CLASS_MEMBER || node->nodeType == PNT_STATIC_CLASS_MEMBER || node->nodeType == PNT_KEY_VALUE ||
          node->nodeType == PNT_VAR_DECLARATOR) &&
          node->children.size() == 2 && (node->children[1]->nodeType == PNT_TABLE_CREATION ||
            node->children[1]->nodeType == PNT_CLASS || node->children[1]->nodeType == PNT_LOCAL_CLASS)))
      {
        vector<string> p = node_to_path(node->children[0]);

        if ((node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NEWSLOT) ||
          (node->nodeType == PNT_FUNCTION))
        {
          if (!p.empty())
            p.pop_back();
        }

        path.insert(path.begin(), p.begin(), p.end());
      }
    }
  }


  int tries = 10;

  do
  {
    if (!extends.empty())
    {
      path = extends;
      extends.clear();
    }

    if (path.size() == 0)
    {
      auto fnd = ident_root.children.find(string(ident));
      if (fnd != ident_root.children.end())
        return true;
    }

    IdentTree * tree = &ident_root;
    for (size_t i = 0; i < path.size(); i++)
    {
      if (!tree)
        return false;

      auto fnd = tree->children.find(string(ident));
      if (fnd != tree->children.end())
        return true;

      if (!tree->extends.empty())
        extends = tree->extends;

      auto it = tree->children.find(path[i]);
      if (it != tree->children.end())
        tree = it->second;
      else
        break;

      if (tree)
      {
        if (!tree->extends.empty())
          extends = tree->extends;

        auto fnd2 = tree->children.find(string(ident));
        if (fnd2 != tree->children.end())
          return true;
      }
    }

    tries--;
  }
  while (!extends.empty() && tries > 0);

  return false;
}


static void dump_ident_root(int indent, IdentTree * tree)
{
  if (!tree)
    return;

  static const char * spaces = "                                                          ";

  for (auto & it : tree->children)
  {
    printf("%.*s", indent, spaces);
    printf("%s\n", it.first.c_str());
    dump_ident_root(indent + 2, it.second);
  }
}



class Analyzer
{
  enum DeclarationContext
  {
    DC_NONE,
    DC_CHILD_NOT_FOUND,
    DC_GLOBAL_VARIABLE,
    DC_CONSTANT,
    DC_GLOBAL_CONSTANT,
    DC_FUNCTION_PARAM,
    DC_CLASS_METHOD,
    DC_CLASS_MEMBER,
    DC_STATIC_CLASS_MEMBER,
    DC_TABLE_MEMBER,
    DC_LOCAL_VARIABLE,
    DC_LOOP_VARIABLE,
    DC_FUNCTION_NAME,
    DC_LOCAL_FUNCTION_NAME,
    DC_CLASS_NAME,
    DC_ENUM_NAME,
    DC_GLOBAL_ENUM_NAME,
    DC_IDENTIFIER,
  };

  const char * declContextToString(DeclarationContext decl_context)
  {
    switch (decl_context)
    {
    case DC_NONE: return "";
    case DC_GLOBAL_VARIABLE: return "global variable";
    case DC_CONSTANT: return "constant";
    case DC_GLOBAL_CONSTANT: return "global constant";
    case DC_FUNCTION_PARAM: return "function parameter";
    case DC_CLASS_METHOD: return "class method";
    case DC_CLASS_MEMBER: return "class member";
    case DC_STATIC_CLASS_MEMBER: return "static class member";
    case DC_TABLE_MEMBER: return "table member";
    case DC_LOCAL_VARIABLE: return "local variable";
    case DC_LOOP_VARIABLE: return "loop variable";
    case DC_FUNCTION_NAME: return "function";
    case DC_LOCAL_FUNCTION_NAME: return "local function";
    case DC_CLASS_NAME: return "class";
    case DC_ENUM_NAME: return "enum";
    case DC_GLOBAL_ENUM_NAME: return "global enum";
    case DC_IDENTIFIER: return "identifier";
    default: return "variable";
    }
  }

  struct IdentifierStruct
  {
    const char * namePtr;
    DeclarationContext declContext;
    const Token * declaredAt;
    const Token * assignedAt;
    const Token * usedAt;
    const Node * loopNode;
    short declDepth;
    short assignDepth;
    short useDepth;
    bool assignedInsideLoop;
    bool isModule;

    IdentifierStruct()
    {
      namePtr = "";
      declContext = DC_NONE;
      declaredAt = nullptr;
      assignedAt = nullptr;
      usedAt = nullptr;
      loopNode = nullptr;
      declDepth = -1;
      assignDepth = -1;
      useDepth = -1;
      assignedInsideLoop = false;
      isModule = false;
    }
  };


  set<const char *> requiredModuleNames;


  bool isNodeEquals(Node * a, Node * b)
  {
    if (a == b)
      return true;

    if (!a || !b)
      return false;

    if (a->nodeType != b->nodeType)
      return false;

    if (a->tok.type != b->tok.type)
      return false;

    if (a->tok.type == TK_FLOAT || a->tok.type == TK_INTEGER)
    {
      if (a->tok.u.i != b->tok.u.i)
        return false;
    }
    else
    {
      if (a->tok.u.s != b->tok.u.s)
        return false;
    }


    if (a->children.size() != b->children.size())
      return false;

    for (size_t i = 0; i < a->children.size(); i++)
      if (!isNodeEquals(a->children[i], b->children[i]))
        return false;

    return true;
  }


  bool isReplaceableType(NodeType type)
  {
    return (type == PNT_NULL || type == PNT_INTEGER || type == PNT_BOOL ||
      type == PNT_STRING || type == PNT_IDENTIFIER || type == PNT_FLOAT || type == PNT_BINARY_OP ||
      type == PNT_UNARY_PRE_OP || type == PNT_UNARY_POST_OP);
  }


  int getNodeDiff(Node * a, Node * b, int cur_diff, int limit)
  {
    if (cur_diff > limit)
      return cur_diff;

    if (a == b)
      return cur_diff;

    if (!a || !b)
      return 9999;

    if (a->children.size() != b->children.size())
      return 9999;

    bool aReplaceableType = isReplaceableType(a->nodeType);
    bool bReplaceableType = isReplaceableType(b->nodeType);

    if (a->nodeType != b->nodeType || a->tok.type != b->tok.type)
    {
      if (aReplaceableType && bReplaceableType)
        cur_diff++;
      else
        return 9999;
    }
    else
    {
      if (a->tok.type == TK_FLOAT || a->tok.type == TK_INTEGER)
      {
        if (a->tok.u.i != b->tok.u.i)
          return cur_diff + 1;
      }
      else
      {
        if (a->tok.u.s != b->tok.u.s)
          return cur_diff + 1;
      }
    }

    for (size_t i = 0; i < a->children.size(); i++)
      cur_diff = getNodeDiff(a->children[i], b->children[i], cur_diff, limit);

    return cur_diff;
  }


  bool existsInTree(Node * search, Node * tree)
  {
    if (isNodeEquals(search, tree))
      return true;

    for (size_t i = 0; i < tree->children.size(); i++)
      if (tree->children[i])
        if (existsInTree(search, tree->children[i]))
          return true;

    return false;
  }

  bool isPotentialyNullable(Node * a)
  {
    if (a->nodeType == PNT_EXPRESSION_PAREN)
      a = a->children[0];

    if (a->nodeType == PNT_NULL)
      return true;

    if (a->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL || a->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
      return true;

    if (a->nodeType == PNT_ACCESS_MEMBER || a->nodeType == PNT_FUNCTION_CALL)
      return isPotentialyNullable(a->children[0]);

    if (a->nodeType == PNT_BINARY_OP && a->tok.type == TK_NULLCOALESCE)
      return isPotentialyNullable(a->children[1]);

    return false;
  }

  bool findIfWithTheSameCondition(Node * condition, Node * if_node)
  {
    if (isNodeEquals(condition, if_node->children[0]))
      return true;

    if (if_node->children.size() == 3 && if_node->children[2] && if_node->children[2]->nodeType == PNT_IF_ELSE)
      return findIfWithTheSameCondition(condition, if_node->children[2]);

    return false;
  }

  void findConditionalExit(bool first_level, Node * node, bool & has_break, bool & has_continue, bool & has_return)
  {
    if (!has_break && node->nodeType == PNT_BREAK)
      has_break = !first_level;
    else if (!has_continue && node->nodeType == PNT_CONTINUE)
      has_continue = !first_level;
    else if (!has_return && node->nodeType == PNT_RETURN)
      has_return = !first_level;
    else if (node->nodeType == PNT_IF_ELSE)
    {
      findConditionalExit(false, node->children[1], has_break, has_continue, has_return);
      if (node->children.size() > 2)
        findConditionalExit(false, node->children[2], has_break, has_continue, has_return);
    }
    else if (node->nodeType == PNT_STATEMENT_LIST)
    {
      for (size_t i = 0; i < node->children.size(); i++)
        findConditionalExit(first_level, node->children[i], has_break, has_continue, has_return);
    }
    else if (node->nodeType == PNT_SWITCH_CASE)
    {
      findConditionalExit(first_level, node->children[1], has_break, has_continue, has_return);
    }
  }

  enum
  {
    RT_NOTHING = 1 << 0,
    RT_NULL = 1 << 1,
    RT_BOOL = 1 << 2,
    RT_NUMBER = 1 << 3,
    RT_STRING = 1 << 4,
    RT_TABLE = 1 << 5,
    RT_ARRAY = 1 << 6,
    RT_CLOSURE = 1 << 7,
    RT_FUNCTION_CALL = 1 << 8,
    RT_UNRECOGNIZED = 1 << 9,
  };

  bool findFunctionReturnTypes(Node * node, unsigned & return_flags)  // returns 'all ways return value'
  {
    if (node->nodeType == PNT_RETURN)
    {
      if (node->children.size() == 0)
      {
        return_flags |= RT_NOTHING;
        return true;
      }

      Node * val = node->children[0];
      if (val->nodeType == PNT_EXPRESSION_PAREN)
        val = val->children[0];

      if (val->nodeType == PNT_NULL)
        return_flags |= RT_NULL;
      else if (val->nodeType == PNT_BOOL)
        return_flags |= RT_BOOL;
      else if (val->nodeType == PNT_INTEGER || val->nodeType == PNT_FLOAT)
        return_flags |= RT_NUMBER;
      else if (val->nodeType == PNT_BINARY_OP && (
        val->tok.type == TK_EQ || val->tok.type == TK_NE || val->tok.type == TK_GT || val->tok.type == TK_GE ||
        val->tok.type == TK_LS || val->tok.type == TK_LE || val->tok.type == TK_IN || val->tok.type == TK_AND ||
        val->tok.type == TK_OR))
      {
        return_flags |= RT_BOOL;
      }
      else if (val->nodeType == PNT_BINARY_OP && (val->tok.type == TK_MINUS || val->tok.type == TK_DIV ||
        val->tok.type == TK_MUL || val->tok.type == TK_BITAND || val->tok.type == TK_BITOR || val->tok.type == TK_BITXOR))
      {
        return_flags |= RT_NUMBER;
      }
      else if (val->nodeType == PNT_UNARY_PRE_OP && (val->tok.type == TK_NOT))
        return_flags |= RT_BOOL;
      else if (val->nodeType == PNT_UNARY_PRE_OP && (val->tok.type == TK_MINUS || val->tok.type == TK_INV))
        return_flags |= RT_NUMBER;
      else if (val->nodeType == PNT_STRING)
        return_flags |= RT_STRING;
      else if (val->nodeType == PNT_ARRAY_CREATION)
        return_flags |= RT_ARRAY;
      else if (val->nodeType == PNT_TABLE_CREATION)
        return_flags |= RT_TABLE;
      else if (val->nodeType == PNT_LAMBDA)
        return_flags |= RT_CLOSURE;
      else if (val->nodeType == PNT_FUNCTION_CALL)
        return_flags |= RT_FUNCTION_CALL;
      else
        return_flags |= RT_UNRECOGNIZED;

      return true;
    }
    else if (node->nodeType == PNT_IF_ELSE)
    {
      bool retThen = findFunctionReturnTypes(node->children[1], return_flags);
      bool retElse = false;
      if (node->children.size() > 2)
        retElse = findFunctionReturnTypes(node->children[2], return_flags);
      return retThen && retElse;
    }
    else if (node->nodeType == PNT_WHILE_LOOP || node->nodeType == PNT_DO_WHILE_LOOP || node->nodeType == PNT_FOR_EACH_LOOP ||
      node->nodeType == PNT_FOR_LOOP)
    {
      for (size_t i = 0; i < node->children.size(); i++)
        if (node->children[i])
          (void)findFunctionReturnTypes(node->children[i], return_flags);
      return false;
    }
    else if (node->nodeType == PNT_STATEMENT_LIST)
    {
      bool retFound = false;
      for (size_t i = 0; i < node->children.size(); i++)
        if (node->children[i])
          retFound |= findFunctionReturnTypes(node->children[i], return_flags);
      return retFound;
    }
    else if (node->nodeType == PNT_SWITCH_STATEMENT)
    {
      bool allReturn = true;
      for (size_t i = 1; i < node->children.size(); i++)
        if (node->children[i] && node->children[i]->children[1])
          allReturn &= findFunctionReturnTypes(node->children[i], return_flags);
      return allReturn;
    }

    return false;
  }

  bool isCallee(Node * node)
  {
    if (node->nodeType == PNT_FUNCTION_CALL)
    {
      node = node->children[0];
      if (node->nodeType == PNT_ACCESS_MEMBER)
        node = node->children[1];
      if (node->nodeType == PNT_IDENTIFIER && !strcmp(node->tok.u.s, "callee"))
        return true;
    }
    return false;
  }

  void checkFunctionCallFormatArguments(Node * fn_call)
  {
    for (size_t i = 1; i < fn_call->children.size() && i < 3; i++)
    {
      Node * arg = fn_call->children[i];
      if (arg->nodeType == PNT_STRING)
      {
        int formatsCount = 0;
        for (const char * p = arg->tok.u.s; *p; p++)
          if (*p == '%')
            if (*(p + 1) == '%')
              p++;
            else
              formatsCount++;

        if (formatsCount > 0 && formatsCount != fn_call->children.size() - i - 1)
        {
          Node * functionNameNode = fn_call->children[0];
          if (functionNameNode->nodeType == PNT_ACCESS_MEMBER || functionNameNode->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL)
            functionNameNode = functionNameNode->children[1];

          if (functionNameNode->nodeType != PNT_IDENTIFIER)
            return;

          string functionName = functionNameNode->tok.u.s;
          std::transform(functionName.begin(), functionName.end(), functionName.begin(), ::tolower);

          if (!!strstr(functionName.c_str(), "prn") ||
            !!strstr(functionName.c_str(), "print") ||
            !!strstr(functionName.c_str(), "form") ||
            !!strstr(functionName.c_str(), "fmt") ||
            !!strstr(functionName.c_str(), "log") ||
            !!strstr(functionName.c_str(), "debug") ||
            !!strstr(functionName.c_str(), "dbg") ||
            !!strstr(functionName.c_str(), "assert"))
          {
            ctx.warning("format-arguments-count", arg->tok);
          }
        }

        return;
      }
    }
  }

  bool isUpperCaseIdentifier(Node * ident)
  {
    if (!ident)
      return false;

    if (ident->nodeType == PNT_ACCESS_MEMBER && ident->children[1]->nodeType == PNT_IDENTIFIER)
      ident = ident->children[1];

    if (ident->nodeType != PNT_IDENTIFIER)
      return false;

    for (const char * p = ident->tok.u.s; *p; p++)
      if (*p >= 'a' && *p <= 'z')
        return false;

    return true;
  }

  bool mustTestForDeclared(Node * ident)
  {
    if (!ident)
      return false;

    if (ident->nodeType != PNT_IDENTIFIER)
      return false;

    if (!strcmp(ident->tok.u.s, "require") || !strcmp(ident->tok.u.s, "require_optional") ||
      !strcmp(ident->tok.u.s, "vargv") || !strcmp(ident->tok.u.s, "persist") || !strcmp(ident->tok.u.s, "getclass"))
    {
      return false;
    }

    if (trusted::trusted_identifiers)
      return true;

    return true;
  }


  bool onlyEmptyStatements(int from, Node * node)
  {
    for (size_t i = from; i < node->children.size(); i++)
      if (node->children[i] && node->children[i]->nodeType != PNT_EMPTY_STATEMENT)
        return false;
    return true;
  }


  bool inWordEnd(const char * name, int pos)
  {
    return (name[pos] == '_' || name[pos] == toupper(name[pos]));
  }

  bool nameLooksLikeResultMustBeBoolean(const char * name)
  {
    if (!name || !name[0])
      return false;

    bool nameInList = false;
    if (strstr(name, "has") == name && inWordEnd(name, 3))
      nameInList = true;
    if (strstr(name, "have") == name && inWordEnd(name, 4))
      nameInList = true;
    else if (strstr(name, "should") == name && inWordEnd(name, 6))
      nameInList = true;
    else if (strstr(name, "need") == name && inWordEnd(name, 4))
      nameInList = true;
    else if (strstr(name, "is") == name && inWordEnd(name, 2))
      nameInList = true;
    else if (strstr(name, "was") == name && inWordEnd(name, 3))
      nameInList = true;

    return nameInList;
  }


  bool nameLooksLikeFunctionMustReturnResult(const char * name)
  {
    if (!name || !name[0])
      return false;

    bool nameInList = nameLooksLikeResultMustBeBoolean(name);

    if (nameInList)
      ;
    else if (strstr(name, "get") == name && (inWordEnd(name, 3) || name[3] == 0))
      nameInList = true;
    else if (strstr(name, "mk") == name && inWordEnd(name, 2))
      nameInList = true;
    else if ((strstr(name, "_ctor") || strstr(name, "Ctor")) && strstr(name, "set") != name)
      nameInList = true;

    return nameInList;
  }


  bool nameLooksLikeResultMustBeUtilised(const char * name)
  {
    bool nameInList = false;
    if (!strcmp(name, "__merge"))
      nameInList = true;
    else if (!strcmp(name, "find") || !strcmp(name, "indexof"))
      nameInList = true;
    else if (!strcmp(name, "searchindex") || !strcmp(name, "findindex") || !strcmp(name, "findvalue"))
      nameInList = true;
    else if (!strcmp(name, "len"))
      nameInList = true;
    else if (!strcmp(name, "reduce"))
      nameInList = true;
    else if (!strcmp(name, "tostring"))
      nameInList = true;
    else if (!strcmp(name, "tointeger"))
      nameInList = true;
    else if (!strcmp(name, "tofloat"))
      nameInList = true;
    else if (!strcmp(name, "slice"))
      nameInList = true;
    else if (!strcmp(name, "tolower"))
      nameInList = true;
    else if (!strcmp(name, "toupper"))
      nameInList = true;
    else if (nameLooksLikeResultMustBeBoolean(name))
      nameInList = true;

    return nameInList;
  }


  bool isStdFunction(const char * name)
  {
    const char * functions[] =
    {
      "seterrorhandler",
      "setdebughook",
      "enabledebuginfo",
      "getstackinfos",
      "getroottable",
      "setroottable",
      "getconsttable",
      "setconsttable",
      "getclass",
      "assert",
      "print",
      "error",
      "compilestring",
      "newthread",
      "suspend",
      "array",
      "type",
      "callee",
      "dummy",
      "collectgarbage",
      "resurrectunreachable",
      "min",
      "max",
      "clamp"
    };

    for (size_t i = 0; i < sizeof(functions) / sizeof(functions[0]); i++)
      if (!strcmp(name, functions[i]))
        return true;

    return false;
  }

  bool canFunctionReturnNull(const char * name)
  {
    const char * functions[] =
    {
      "find",
      "indexof",
      "searchindex",
      "findindex",
      "findvalue",
    };

    for (size_t i = 0; i < sizeof(functions) / sizeof(functions[0]); i++)
      if (!strcmp(name, functions[i]))
        return true;

    return false;
  }

  bool isWatchedVariable(const char * name)
  {
    for (size_t i = 0; i < lexer.tokens.size() - 1; i++)
      if (lexer.tokens[i].type == TK_IDENTIFIER && lexer.tokens[i].u.s == name) // it's ok to compare pointers in this case
      {
        if (lexer.tokens[i + 1].type == TK_ASSIGN)
        {
          int line = lexer.tokens[i + 2].line;
          for (int j = i + 2; j < lexer.tokens.size() - 1; j++)
          {
            if (lexer.tokens[j].line != line)
              break;
            if (lexer.tokens[j].type == TK_IDENTIFIER && !strcmp(lexer.tokens[j].u.s, "Watched"))
              return true;
          }
        }
        else if (lexer.tokens[i + 1].type == TK_DOT && lexer.tokens[i + 2].type == TK_IDENTIFIER)
        {
          const char * s = lexer.tokens[i + 2].u.s;
          if (!strcmp(s, "update") || !strcmp(s, "value"))
            return true;
        }
        else if (lexer.tokens[i + 1].type == TK_LPAREN &&
          (lexer.tokens[i + 2].type == TK_TRUE || lexer.tokens[i + 2].type == TK_FALSE) &&
          lexer.tokens[i + 3].type == TK_RPAREN)
        {
          return true;
        }
      }

    return false;
  }


  Token * getPrevToken(Token * tok_ptr)
  {
    if (&lexer.tokens[0] < tok_ptr)
      return tok_ptr - 1;
    else
      return nullptr;
  }

  void checkUnutilizedResult(Node * node)
  {
    if (!node)
      return;

    if (node->nodeType == PNT_FLOAT || node->nodeType == PNT_INTEGER || node->nodeType == PNT_BOOL ||
      node->nodeType == PNT_STRING)
    {
      ctx.warning("result-not-utilized", node->tok);
      return;
    }

    if (node->nodeType == PNT_FUNCTION_CALL && node->children[0]->nodeType == PNT_IDENTIFIER)
    {
      const char * functionName = node->children[0]->tok.u.s;
      if (nameLooksLikeResultMustBeUtilised(functionName))
      {
        if (!isWatchedVariable(functionName))
        {
          ctx.warning("named-like-should-return", node->tok, functionName);
          return;
        }
      }
    }

    if (node->nodeType == PNT_FUNCTION_CALL &&
      (node->children[0]->nodeType == PNT_ACCESS_MEMBER || node->children[0]->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL) &&
      node->children[0]->children[1]->nodeType == PNT_IDENTIFIER)
    {
      const char * functionName = node->children[0]->children[1]->tok.u.s;
      if (nameLooksLikeResultMustBeUtilised(functionName))
      {
        if (!isWatchedVariable(functionName))
        {
          ctx.warning("named-like-should-return", node->tok, functionName);
          return;
        }
      }
    }

    if (node->nodeType == PNT_BINARY_OP || node->nodeType == PNT_TERNARY_OP ||
      node->nodeType == PNT_UNARY_PRE_OP || node->nodeType == PNT_IDENTIFIER ||
      node->nodeType == PNT_ACCESS_MEMBER || node->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL)
    {
      TokenType t = node->tok.type;
      if (t == TK_3WAYSCMP || t == TK_AND || t == TK_OR || t == TK_IN || t == TK_EQ || t == TK_NE || t == TK_LE ||
        t == TK_LS || t == TK_GT || t == TK_GE || t == TK_NOT || t == TK_INV || t == TK_BITAND || t == TK_BITOR ||
        t == TK_BITXOR || t == TK_DIV || t == TK_MODULO || t == TK_INSTANCEOF || t == TK_QMARK || t == TK_MINUS ||
        t == TK_PLUS || t == TK_MUL || t == TK_SHIFTL || t == TK_SHIFTR || t == TK_USHIFTR || t == TK_TYPEOF ||
        t == TK_CLONE ||
        node->nodeType == PNT_IDENTIFIER || node->nodeType == PNT_ACCESS_MEMBER ||
        node->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL)
      {
        ctx.warning("result-not-utilized", node->tok);
      }
    }
  }


  bool isSuspiciousNeighborOfNullCoalescing(TokenType t)
  {
    return (t == TK_3WAYSCMP || t == TK_AND || t == TK_OR || t == TK_IN || t == TK_EQ || t == TK_NE || t == TK_LE ||
      t == TK_LS || t == TK_GT || t == TK_GE || t == TK_NOT || t == TK_INV || t == TK_BITAND || t == TK_BITOR ||
      t == TK_BITXOR || t == TK_DIV || t == TK_MODULO || t == TK_INSTANCEOF || t == TK_QMARK || t == TK_MINUS ||
      t == TK_PLUS || t == TK_MUL || t == TK_SHIFTL || t == TK_SHIFTR || t == TK_USHIFTR);
  }

  vector<Node *> nodePath;

public:
  CompilationContext & ctx;
  Lexer & lexer;

  Analyzer(Lexer & lexer_) :
    ctx(lexer_.getCompilationContext()),
    lexer(lexer_)
  {
    for (int i = 0; i < 16; i++)
      nodePath.push_back(nullptr);
  }


  bool isTestPresentInNodePath(Node * nextNode = nullptr)
  {
    for (size_t i = nodePath.size() - 1; nodePath[i] != nullptr; nextNode = nodePath[i], i--)
    {
      if ((nodePath[i]->nodeType == PNT_IF_ELSE || nodePath[i]->nodeType == PNT_TERNARY_OP ||
        nodePath[i]->nodeType == PNT_WHILE_LOOP) &&
        nextNode && nodePath[i]->children[0] == nextNode)
      {
        return true;
      }
    }

    return false;
  }


  bool isSubnodeExistsInNode(Node * node, Node * subnode)
  {
    if (isNodeEquals(node, subnode))
      return true;

    for (size_t i = 0; i < node->children.size(); i++)
      if (node->children[i])
        if (isSubnodeExistsInNode(node->children[i], subnode))
          return true;

    return false;
  }


  bool isVariableTestedBefore(Node * variable)
  {
    Node * nextNode = nullptr;
    for (size_t i = nodePath.size() - 1; nodePath[i] != nullptr; nextNode = nodePath[i], i--)
    {
      if (nodePath[i]->nodeType == PNT_IF_ELSE || nodePath[i]->nodeType == PNT_TERNARY_OP ||
        nodePath[i]->nodeType == PNT_WHILE_LOOP)
      {
        Node * condition = nodePath[i]->children[0];
        if (isSubnodeExistsInNode(condition, variable))
          return true;
      }
    }

    return false;
  }



  const char * getFunctionName(Node * node)
  {
    if (node->nodeType == PNT_FUNCTION_CALL || node->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
    {
      Node * functionNameNode = node->children[0];

      if (functionNameNode)
      {
        if (functionNameNode->nodeType == PNT_ACCESS_MEMBER || functionNameNode->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL)
          functionNameNode = functionNameNode->children[1];

        if (functionNameNode->nodeType == PNT_IDENTIFIER)
        {
          const char * functionName = functionNameNode->tok.u.s;
          return functionName;
        }
      }
    }

    return "";
  }


  void updateNearestAssignments(Node * node)
  {
    if (!node)
    {
      nearest_assignments.clear();
      return;
    }

    if (node->nodeType == PNT_LOCAL_VAR_DECLARATION)
    {
      for (size_t i = 0; i < node->children.size(); i++)
      {
        Node * decl = node->children[i];
        if (!decl)
          continue;

        if (decl->nodeType != PNT_VAR_DECLARATOR || decl->children.size() <= 1)
          continue;

        if (decl->children[0]->nodeType == PNT_LIST_OF_KEYS_ARRAY || decl->children[0]->nodeType == PNT_LIST_OF_KEYS_TABLE)
        {
          decl = decl->children[0];
          for (size_t j = 0; j < decl->children.size(); j++)
          {
            Node * listDecl = decl->children[i];
            if (!listDecl)
              continue;

            if (listDecl->nodeType != PNT_VAR_DECLARATOR || listDecl->children.size() <= 1)
              continue;
            nearest_assignments.push_back(std::make_pair(listDecl->children[0], std::make_pair(listDecl->children[1], true)));
          }
        }
        else if (decl->children[0]->nodeType == PNT_IDENTIFIER)
        {
          nearest_assignments.push_back(std::make_pair(decl->children[0], std::make_pair(decl->children[1], false)));
        }
      }
    }
    else if (node->nodeType == PNT_FUNCTION_PARAMETER)
    {
      if (node->children.size() > 1)
        nearest_assignments.push_back(std::make_pair(node->children[0], std::make_pair(node->children[1], true)));
      else
        removeNearestAssignmentsFoundAt(node);

      if (node->children[0]->nodeType == PNT_LIST_OF_KEYS_ARRAY || node->children[0]->nodeType == PNT_LIST_OF_KEYS_TABLE)
        for (size_t j = 0; j < node->children[0]->children.size(); j++)
        {
          Node * n = node->children[0]->children[j];
          if (n->children.size() > 1)
            nearest_assignments.push_back(std::make_pair(n->children[0], std::make_pair(n->children[1], true)));
          else
            removeNearestAssignmentsFoundAt(n);
        }
    }
    else if (node->nodeType == PNT_BINARY_OP)
    {
      if (node->tok.type == TK_ASSIGN || node->tok.type == TK_NEWSLOT)
        nearest_assignments.push_back(std::make_pair(node->children[0], std::make_pair(node->children[1], false)));
    }
  }

  void removeNearestAssignmentsFoundAt(Node * node)
  {
    if (!nearest_assignments.size() || !node)
      return;

    for (size_t i = 0; i < nearest_assignments.size(); i++)
      if (nearest_assignments[i].first)
        if (isNodeEquals(nearest_assignments[i].first, node))
          nearest_assignments[i].first = nullptr;

    for (size_t i = 0; i < node->children.size(); i++)
      removeNearestAssignmentsFoundAt(node->children[i]);
  }

  void removeNearestAssignmentsExcludeString(Node * node)
  {
    if (!nearest_assignments.size() || !node)
      return;

    for (size_t i = 0; i < nearest_assignments.size(); i++)
      if (nearest_assignments[i].first)
        if (isNodeEquals(nearest_assignments[i].first, node))
        {
          Node * n = tryReplaceVar(node, true);
          if (!isVarCanBeString(n))
            nearest_assignments[i].first = nullptr;
        }

    for (size_t i = 0; i < node->children.size(); i++)
      removeNearestAssignmentsExcludeString(node->children[i]);
  }

  void removeNearestAssignmentsMod(Node * node)
  {
    if (!nearest_assignments.size() || !node)
      return;

    if ((node->nodeType == PNT_BINARY_OP &&
      (node->tok.type == TK_NEWSLOT || node->tok.type == TK_ASSIGN || node->tok.type == TK_PLUSEQ ||
        node->tok.type == TK_MINUSEQ || node->tok.type == TK_MULEQ || node->tok.type == TK_DIVEQ))
      ||
      ((node->nodeType == PNT_UNARY_PRE_OP || node->nodeType == PNT_UNARY_POST_OP) &&
      (node->tok.type == TK_PLUSPLUS || node->tok.type == TK_MINUSMINUS)))
    {
      for (size_t i = 0; i < nearest_assignments.size(); i++)
        if (nearest_assignments[i].first)
          if (isNodeEquals(nearest_assignments[i].first, node->children[0]))
            nearest_assignments[i].first = nullptr;
    }

    for (size_t i = 0; i < node->children.size(); i++)
      removeNearestAssignmentsMod(node->children[i]);
  }

  void removeNearestAssignmentsTestNull(Node * node_, bool condition_root = true)
  {
    if (!nearest_assignments.size() || !node_)
      return;

    Node * tests[2] = { nullptr, node_ };

    if (condition_root && (node_->nodeType == PNT_IDENTIFIER || node_->nodeType == PNT_ACCESS_MEMBER))
    {
      Node * replaced = tryReplaceVar(node_, false);
      if (replaced != node_)
        tests[0] = replaced;
    }

    for (int tr = 0; tr < 2; tr++)
    {
      Node * node = tests[tr];
      if (!node)
        continue;

      Node * nodeToCheck = nullptr;
      if ((node->nodeType == PNT_BINARY_OP && node->tok.type == TK_AND) ||
        (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NE && node->children[1]->tok.type == TK_NULL) ||
        (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_EQ && node->children[1]->tok.type == TK_NULL) ||
        (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_IN) ||
        (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_INSTANCEOF) ||
        (node->nodeType == PNT_UNARY_PRE_OP && node->tok.type == TK_NOT) ||
        (node->nodeType == PNT_UNARY_PRE_OP && node->tok.type == TK_TYPEOF) ||
        node->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL)
      {
        nodeToCheck = node->children[0];
      }

      if (condition_root && (node->nodeType == PNT_IDENTIFIER || node->nodeType == PNT_ACCESS_MEMBER))
        nodeToCheck = node;

      if (nodeToCheck)
      {
        for (size_t i = 0; i < nearest_assignments.size(); i++)
          if (nearest_assignments[i].first)
            if (isNodeEquals(nearest_assignments[i].first, nodeToCheck))
              nearest_assignments[i].first = nullptr;
      }

      for (size_t i = 0; i < node->children.size(); i++)
        removeNearestAssignmentsTestNull(node->children[i], false);
    }
  }

  Node * tryReplaceVar(Node * node, bool accept_optional)
  {
    if (!node)
      return nullptr;

    for (int i = int(nearest_assignments.size()) - 1; i >= 0; i--)
      if (nearest_assignments[i].first && isNodeEquals(node, nearest_assignments[i].first))
      {
        bool optional = nearest_assignments[i].second.second;
        if (accept_optional || !optional)
          return nearest_assignments[i].second.first;
        break;
      }

    return node;
  }

  bool isVarCanBeNull(Node * node)
  {
    if (!node)
      return false;

    if (node->nodeType == PNT_NULL)
      return true;

    for (int i = int(nearest_assignments.size()) - 1; i >= 0; i--)
      if (nearest_assignments[i].first && isNodeEquals(node, nearest_assignments[i].first))
      {
        if (nearest_assignments[i].second.first->nodeType == PNT_NULL)
          return true;
        break;
      }

    return false;
  }

  bool isVarCanBeString(Node * node)
  {
    if (!node)
      return false;

    if (node->nodeType == PNT_STRING)
      return true;

    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NULLCOALESCE &&
      node->children[0]->nodeType == PNT_STRING)
    {
      return isVarCanBeString(node->children[0]);
    }

    if (node->nodeType == PNT_FUNCTION_CALL && node->children[0]->nodeType == PNT_ACCESS_MEMBER &&
      node->children[0]->children[1]->nodeType == PNT_IDENTIFIER)
    {
      const char * fnName = node->children[0]->children[1]->tok.u.s;
      if (
        !strcmp(fnName, "subst") ||
        !strcmp(fnName, "concat") ||
        !strcmp(fnName, "tostring") ||
        !strcmp(fnName, "toupper") ||
        !strcmp(fnName, "tolower") ||
        !strcmp(fnName, "slice") ||
        !strcmp(fnName, "trim") ||
        !strcmp(fnName, "join") ||
        !strcmp(fnName, "loc") ||
        !strcmp(fnName, "format") ||
        !strcmp(fnName, "replace")
        )
      {
        return true;
      }
    }

    if (node->nodeType == PNT_FUNCTION_CALL && node->children[0]->nodeType == PNT_IDENTIFIER)
    {
      const char * fnName = node->children[0]->tok.u.s;
      if (
        !strcmp(fnName, "loc")
        )
      {
        return true;
      }
    }



    for (int i = int(nearest_assignments.size()) - 1; i >= 0; i--)
      if (nearest_assignments[i].first && isNodeEquals(node, nearest_assignments[i].first))
      {
        if (nearest_assignments[i].second.first->nodeType == PNT_STRING)
          return true;
        break;
      }

    return false;
  }


  Node * extractFunction(Node * node)
  {
    if (node->nodeType == PNT_FUNCTION || node->nodeType == PNT_LOCAL_FUNCTION || node->nodeType == PNT_LAMBDA ||
      node->nodeType == PNT_CLASS_METHOD)
    {
      return node;
    }

    if (node->nodeType == PNT_KEY_VALUE || node->nodeType == PNT_CLASS_MEMBER || node->nodeType == PNT_STATIC_CLASS_MEMBER ||
      node->nodeType == PNT_VAR_DECLARATOR)
    {
      if (node->children.size() > 1 && node->children[1])
        return extractFunction(node->children[1]);
    }

    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_NEWSLOT || node->tok.type == TK_ASSIGN))
      return extractFunction(node->children[1]);

    if (node->nodeType == PNT_LOCAL_VAR_DECLARATION && node->children.size() > 0)
      return extractFunction(node->children[0]);

    return nullptr;
  }


  Node * extractAssignedExpression(Node * node)
  {
    if (node->nodeType == PNT_KEY_VALUE || node->nodeType == PNT_CLASS_MEMBER || node->nodeType == PNT_STATIC_CLASS_MEMBER ||
      node->nodeType == PNT_VAR_DECLARATOR)
    {
      if (node->children.size() > 1 && node->children[1])
        return node->children[1];
    }

    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_NEWSLOT || node->tok.type == TK_ASSIGN))
      return node->children[1];

    if (node->nodeType == PNT_LOCAL_VAR_DECLARATION && node->children.size() > 0)
      return extractAssignedExpression(node->children[0]);

    return nullptr;
  }


  int getComplexity(Node * node, int cur_complexity, int limit)
  {
    if (!node)
      return cur_complexity;

    if (cur_complexity > limit)
      return cur_complexity;

    cur_complexity += int(node->children.size());
    if (cur_complexity > limit)
      return cur_complexity;

    for (size_t i = 0; i < node->children.size(); i++)
      if (node->children[i])
      {
        cur_complexity = getComplexity(node->children[i], cur_complexity, limit);
        if (node->children[i]->nodeType == PNT_FUNCTION_CALL || node->children[i]->nodeType == PNT_ACCESS_MEMBER ||
          node->children[i]->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL ||
          node->children[i]->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL)
        {
          cur_complexity--;
        }

        if (cur_complexity > limit)
          return cur_complexity;
      }

    return cur_complexity;
  }


  void check(Node * node)
  {
    nodePath.push_back(node);

    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_OR)
      if (node->children[0]->tok.type == TK_AND || node->children[1]->tok.type == TK_AND)
        ctx.warning("and-or-paren", node->tok);

    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_OR || node->tok.type == TK_AND))
      if (node->children[0]->tok.type == TK_BITAND || node->children[1]->tok.type == TK_BITAND ||
          node->children[0]->tok.type == TK_BITOR || node->children[1]->tok.type == TK_BITOR
         )
      {
        ctx.warning("bitwise-bool-paren", node->tok);
      }

    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_BITOR || node->tok.type == TK_BITAND || node->tok.type == TK_BITXOR))
    {
      Node * left = node->children[0];
      Node * right = node->children[1];
      if (left->nodeType == PNT_EXPRESSION_PAREN)
        left = left->children[0];
      if (right->nodeType == PNT_EXPRESSION_PAREN)
        right = right->children[0];

      left = tryReplaceVar(left, true);
      right = tryReplaceVar(right, true);

      TokenType leftTok = left->tok.type;
      TokenType rightTok = right->tok.type;

      if (leftTok == TK_EQ || rightTok == TK_EQ ||
        leftTok == TK_NE || rightTok == TK_NE ||
        leftTok == TK_LE || rightTok == TK_LE ||
        leftTok == TK_GT || rightTok == TK_GT ||
        leftTok == TK_LS || rightTok == TK_LS ||
        leftTok == TK_TRUE || rightTok == TK_TRUE ||
        leftTok == TK_FALSE || rightTok == TK_FALSE ||
        leftTok == TK_NOT || rightTok == TK_NOT
        )
      {
        ctx.warning("bitwise-apply-to-bool", node->tok);
      }
    }

    if (node->nodeType == PNT_STATEMENT_LIST && node->children.size() > 1)
      for (size_t i = 0; i < node->children.size() - 1; i++)
        if (node->children[i]->nodeType == PNT_RETURN &&
          node->children[i + 1]->nodeType != PNT_BREAK &&
          !onlyEmptyStatements(int(i + 1), node))
        {
          ctx.warning("unreachable-code", node->children[i + 1]->tok);
        }

    if (node->nodeType == PNT_STATEMENT_LIST && node->children.size() > 1)
    {
      for (size_t i = 0; i < node->children.size() - 1; i++)
      {
        if (node->children[i]->nodeType == PNT_BINARY_OP && node->children[i]->tok.type == TK_ASSIGN)
          for (size_t j = i + 1; j < node->children.size(); j++)
            if (node->children[j]->nodeType == PNT_BINARY_OP && node->children[j]->tok.type == TK_ASSIGN)
            {
              if (isNodeEquals(node->children[i]->children[0], node->children[j]->children[0]))
              {
                if (!existsInTree(node->children[i]->children[0], node->children[j]->children[1]))
                  ctx.warning("assigned-twice", node->children[j]->children[0]->tok);
              }
            }
            else
            {
              break;
            }
      }
    }

/*    if (node->nodeType == PNT_STATEMENT_LIST && node->children.size() > 1)
      for (size_t i = 0; i < node->children.size() - 1; i++)
        if (node->children[i]->nodeType == PNT_IF_ELSE && node->children[i + 1]->nodeType == PNT_IF_ELSE)
          if (node->children[i]->children[0]->nodeType != PNT_IDENTIFIER) // check only compex expressions
            if (isNodeEquals(node->children[i]->children[0], node->children[i + 1]->children[0]))
            {
              ctx.warning(207, "The conditional expressions of the 'if' statements situated alongside each other are identical"
              "(if (A); if (A);).",
                node->children[i]->tok);
            }*/


    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NEWSLOT && node->children[0]->nodeType == PNT_IDENTIFIER)
      ctx.warning("global-var-creation", node->tok);


    if (node->nodeType == PNT_BINARY_OP && (is_arith_op_token(node->tok.type)))
    {
      Node * left = tryReplaceVar(node->children[0], true);
      Node * right = tryReplaceVar(node->children[1], true);
      if (isPotentialyNullable(left))
      {
        bool tested = (node->children[0]->nodeType == PNT_IDENTIFIER) && isVariableTestedBefore(node->children[0]);
        if (!tested)
          ctx.warning("potentially-nulled-arith", node->tok);
      }

      if (isPotentialyNullable(right))
      {
        bool tested = (node->children[1]->nodeType == PNT_IDENTIFIER) && isVariableTestedBefore(node->children[1]);
        if (!tested)
          ctx.warning("potentially-nulled-arith", node->tok);
      }
    }

    if (node->nodeType == PNT_BINARY_OP && (is_cmp_op_token(node->tok.type)))
    {
      Node * left = tryReplaceVar(node->children[0], true);
      Node * right = tryReplaceVar(node->children[1], true);
      if (isPotentialyNullable(left))
      {
        bool tested = (node->children[0]->nodeType == PNT_IDENTIFIER) && isVariableTestedBefore(node->children[0]);
        if (!tested)
          ctx.warning("potentially-nulled-cmp", node->tok);
      }

      if (isPotentialyNullable(right))
      {
        bool tested = (node->children[1]->nodeType == PNT_IDENTIFIER) && isVariableTestedBefore(node->children[1]);
        if (!tested)
          ctx.warning("potentially-nulled-cmp", node->tok);
      }
    }


    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_ASSIGN || node->tok.type == TK_NEWSLOT ||
        node->tok.type == TK_PLUSEQ || node->tok.type == TK_MINUSEQ || node->tok.type == TK_MULEQ ||
        node->tok.type == TK_DIVEQ || node->tok.type == TK_MODEQ
       ))
    {
      if (isPotentialyNullable(node->children[0]))
        ctx.warning("potentially-nulled-assign", node->tok);

      if (node->tok.type != TK_ASSIGN && node->tok.type != TK_NEWSLOT)
      {
        Node * right = tryReplaceVar(node->children[1], true);
        if (isPotentialyNullable(node->children[1]))
        {
          bool tested = (node->children[1]->nodeType == PNT_IDENTIFIER) && isVariableTestedBefore(node->children[1]);
          if (!tested)
            ctx.warning("potentially-nulled-arith", node->tok);
        }
      }
    }

    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_ASSIGN)
    {
      Node * left = node->children[0];
      Node * right = node->children[1];
      if (left->nodeType == PNT_EXPRESSION_PAREN)
        left = left->children[0];
      if (right->nodeType == PNT_EXPRESSION_PAREN)
        right = right->children[0];

      if (isNodeEquals(left, right))
        ctx.warning("assigned-to-itself", node->tok);
    }

    if (node->nodeType == PNT_ACCESS_MEMBER && node->tok.type == TK_LSQUARE &&
      node->children[0]->nodeType != PNT_ACCESS_MEMBER_IF_NOT_NULL)
    {
      Node * n = tryReplaceVar(node->children[1], true);
      if (isPotentialyNullable(n))
      {
        bool tested = (node->children[1]->nodeType == PNT_IDENTIFIER) && isVariableTestedBefore(node->children[1]);
        if (!tested)
          ctx.warning("potentially-nulled-index", node->tok);
      }
    }

    if (node->nodeType == PNT_SWITCH_STATEMENT && node->children.size() > 2)
      for (size_t i = 1; i < node->children.size() - 1; i++)
        for (size_t j = i + 1; j < node->children.size(); j++)
          if (isNodeEquals(node->children[i]->children[0], node->children[j]->children[0]))
            ctx.warning("duplicate-case", node->children[j]->children[0]->tok);

    if (node->nodeType == PNT_IF_ELSE && node->children.size() == 3 && node->children[2] && node->children[2]->nodeType == PNT_IF_ELSE)
      if (findIfWithTheSameCondition(node->children[0], node->children[2]))
        ctx.warning("duplicate-if-expression", node->children[0]->tok);

    if (node->nodeType == PNT_IF_ELSE && node->children.size() == 3 && node->children[2])
      if (isNodeEquals(node->children[1], node->children[2]))
        ctx.warning("then-and-else-equals", node->children[2]->tok);

    if (node->nodeType == PNT_TERNARY_OP)
    {
      Node * ifTrue = tryReplaceVar(node->children[1], false);
      Node * ifFalse = tryReplaceVar(node->children[2], false);
      if (isNodeEquals(ifTrue, ifFalse))
        ctx.warning("operator-returns-same-val", node->tok);
    }

    if (node->nodeType == PNT_TERNARY_OP)
      if (node->children[0]->nodeType == PNT_BINARY_OP &&
        (node->children[0]->tok.type == TK_PLUS || node->children[0]->tok.type == TK_MINUS || node->children[0]->tok.type == TK_MUL ||
          node->children[0]->tok.type == TK_DIV || node->children[0]->tok.type == TK_BITOR ||
          node->children[0]->tok.type == TK_BITAND || node->children[0]->tok.type == TK_MODULO ||
          node->children[0]->tok.type == TK_SHIFTL || node->children[0]->tok.type == TK_SHIFTR ||
          node->children[0]->tok.type == TK_USHIFTR || node->children[0]->tok.type == TK_3WAYSCMP))
      {
        bool ignore = (node->children[0]->tok.type == TK_BITAND) &&
          (isUpperCaseIdentifier(node->children[0]->children[0]) || isUpperCaseIdentifier(node->children[0]->children[1]) ||
            node->children[0]->children[1]->nodeType == PNT_INTEGER);

        if (!ignore)
          ctx.warning("ternary-priority", node->tok, token_strings[node->children[0]->tok.type]);
      }


    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NULLCOALESCE)
    {
      if (node->children[0]->nodeType == PNT_BINARY_OP && isSuspiciousNeighborOfNullCoalescing(node->children[0]->tok.type))
        ctx.warning("null-coalescing-priority", node->tok, token_strings[node->children[0]->tok.type]);

      if (node->children[1]->nodeType == PNT_BINARY_OP && isSuspiciousNeighborOfNullCoalescing(node->children[1]->tok.type))
        ctx.warning("null-coalescing-priority", node->tok, token_strings[node->children[1]->tok.type]);
    }


    if (node->nodeType == PNT_FUNCTION_CALL || node->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
      if (node->children.size() >= 2 && node->children[0] && node->children[1])
        if (node->children[0]->nodeType == PNT_ACCESS_MEMBER && node->children[1]->nodeType == PNT_ARRAY_CREATION &&
          node->children[0]->children[1]->nodeType == PNT_IDENTIFIER && !strcmp(node->children[0]->children[1]->tok.u.s, "extend"))
        {
          ctx.warning("extent-to-append", node->children[0]->children[1]->tok);
        }


    if (node->nodeType == PNT_STRING)
    {
      int d = 0;
      for (int i = 0; i < 8; i++)
      {
        if (nodePath[nodePath.size() - 2 - d] && nodePath[nodePath.size() - 2 - d]->nodeType == PNT_BINARY_OP)
          d++;
        else
          break;
      }

      d = (nodePath[nodePath.size() - 2 - d] && nodePath[nodePath.size() - 2 - d]->nodeType == PNT_EXPRESSION_PAREN) ? d + 1 : d;

      bool isSubst = nodePath[nodePath.size() - 2 - d]->nodeType == PNT_ACCESS_MEMBER &&
        nodePath[nodePath.size() - 3 - d] && (nodePath[nodePath.size() - 3 - d]->nodeType == PNT_FUNCTION_CALL ||
          nodePath[nodePath.size() - 3 - d]->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL);

      if (!isSubst)
      {
        const char * bracePtr = strchr(node->tok.u.s, '{');
        if (bracePtr && (isalpha(bracePtr[1]) || bracePtr[1] == '_'))
        {
          bool isBlk = (strstr(node->tok.u.s, ":i=") || strstr(node->tok.u.s, ":r=") || strstr(node->tok.u.s, ":t=") ||
            strstr(node->tok.u.s, ":p2=") || strstr(node->tok.u.s, ":p3=") || strstr(node->tok.u.s, ":tm="));
          if (!isBlk && bracePtr[1] && strchr(bracePtr + 2, '}'))
          {
            const char * functionName = nodePath[nodePath.size() - 2]->nodeType == PNT_FUNCTION_CALL ?
              getFunctionName(nodePath[nodePath.size() - 2]) : "";

            bool ok = !strcmp(functionName, "loc") || !strcmp(functionName, "split") || !strcmp(functionName, "assert");
            if (!ok)
              ctx.warning("forgot-subst", node->tok);
          }
        }
      }
    }


    if (node->nodeType == PNT_BINARY_OP)
      if (node->tok.type == TK_EQ || node->tok.type == TK_LE || node->tok.type == TK_GE || node->tok.type == TK_LS ||
        node->tok.type == TK_GT || node->tok.type == TK_NE || node->tok.type == TK_AND || node->tok.type == TK_OR ||
        node->tok.type == TK_MINUS || node->tok.type == TK_3WAYSCMP || node->tok.type == TK_DIV ||
        node->tok.type == TK_MODULO || node->tok.type == TK_BITOR || node->tok.type == TK_BITAND || node->tok.type == TK_BITXOR ||
        node->tok.type == TK_SHIFTL || node->tok.type == TK_SHIFTR || node->tok.type == TK_USHIFTR)
      {
        Node * left = (node->children[0]);
        Node * right = (node->children[1]);

        if (left->nodeType == PNT_EXPRESSION_PAREN)
          left = left->children[0];
        if (right->nodeType == PNT_EXPRESSION_PAREN)
          right = right->children[0];

        if (isNodeEquals(left, right))
          if (left->nodeType != PNT_INTEGER && left->nodeType != PNT_FLOAT)
            ctx.warning("same-operands", node->tok, token_strings[node->tok.type]);
      }


    if (node->nodeType == PNT_STATEMENT_LIST)
    {
      for (size_t i = 1; i < node->children.size(); i++)
        if (node->children[i] && node->children[i]->nodeType == PNT_WHILE_LOOP && node->children[i - 1]->nodeType == PNT_STATEMENT_LIST)
          ctx.warning("forgotten-do", node->children[i]->tok);
    }


    if (node->nodeType == PNT_DO_WHILE_LOOP || node->nodeType == PNT_WHILE_LOOP || node->nodeType == PNT_FOR_EACH_LOOP ||
      node->nodeType == PNT_FOR_LOOP)
    {
      Node * statements = nullptr;
      if (node->nodeType == PNT_DO_WHILE_LOOP || node->nodeType == PNT_WHILE_LOOP)
        statements = node->children[1];
      if (node->nodeType == PNT_FOR_EACH_LOOP || node->nodeType == PNT_FOR_LOOP)
        statements = node->children[3];

      Token * uncReturn = nullptr;
      Token * uncContinue = nullptr;
      Token * uncBreak = nullptr;

      if (statements->nodeType == PNT_STATEMENT_LIST)
      {
        for (size_t i = 0; i < statements->children.size(); i++)
        {
          if (statements->children[i]->nodeType == PNT_RETURN)
            uncReturn = &(statements->children[i]->tok);
          if (statements->children[i]->nodeType == PNT_CONTINUE)
            uncContinue = &(statements->children[i]->tok);
          if (statements->children[i]->nodeType == PNT_BREAK)
            uncBreak = &(statements->children[i]->tok);
        }
      }

      bool conditionalBreak = false;
      bool conditionalContinue = false;
      bool conditionalReturn = false;
      if (uncReturn || uncContinue || uncBreak)
        findConditionalExit(false, statements, conditionalBreak, conditionalContinue, conditionalReturn);

      if (uncReturn)
        if (!conditionalBreak && !conditionalContinue && node->nodeType != PNT_FOR_EACH_LOOP)
          ctx.warning("unconditional-return-loop", *uncReturn);

      if (uncContinue)
        if (!conditionalBreak && !conditionalReturn)
          ctx.warning("unconditional-continue-loop", *uncContinue);

      if (uncBreak)
        if (!conditionalContinue && !conditionalReturn && node->nodeType != PNT_FOR_EACH_LOOP)
          ctx.warning("unconditional-break-loop", *uncBreak);
    }


    if (node->nodeType == PNT_FOR_EACH_LOOP)
    {
      Node * n = tryReplaceVar(node->children[2], true);
      if (isPotentialyNullable(n))
        ctx.warning("potentially-nulled-container", node->children[2]->tok);
    }


    if (nodePath[nodePath.size() - 2] && (nodePath[nodePath.size() - 2]->nodeType == PNT_ARRAY_CREATION ||
      nodePath[nodePath.size() - 2]->nodeType == PNT_FUNCTION_CALL))
    {
      Token * t = getPrevToken(&node->tok);
      if (t)
      {
        if (node->nodeType == PNT_FUNCTION_CALL && (t->nextSpace || t->nextEol))
          ctx.warning("parsed-function-call", node->tok);

        if (node->nodeType == PNT_ACCESS_MEMBER && (t->nextSpace || t->nextEol) && node->tok.type == TK_LSQUARE)
          ctx.warning("parsed-access-member", node->tok);

        if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_PLUS || node->tok.type == TK_MINUS) &&
          (t->nextEol || t->nextSpace) && (!node->tok.nextEol && !node->tok.nextSpace))
        {
          if (node->children[1]->nodeType != PNT_STRING)
            ctx.warning("not-unary-op", node->tok, (node->tok.type == TK_PLUS) ? "+" : "-");
        }
      }
    }


    {
      if (node->nodeType == PNT_STATEMENT_LIST)
        for (size_t i = 0; i < node->children.size(); i++)
          checkUnutilizedResult(node->children[i]);

      if (node->nodeType == PNT_IF_ELSE)
      {
        checkUnutilizedResult(node->children[1]);
        if (node->children.size() > 2)
          checkUnutilizedResult(node->children[2]);
      }

      if (node->nodeType == PNT_SWITCH_CASE)
        if (node->children.size() > 1)
          checkUnutilizedResult(node->children[1]);
    }


    if ((node->nodeType == PNT_ACCESS_MEMBER || node->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL) &&
      (node->tok.type == TK_LSQUARE || node->tok.type == TK_NULLGETOBJ))
    {
      Node * n = tryReplaceVar(node->children[1], true);

      if (n->nodeType == PNT_BINARY_OP)
      {
        TokenType t = n->tok.type;
        if (t == TK_AND || t == TK_OR || t == TK_IN || t == TK_EQ || t == TK_NE || t == TK_LE || t == TK_LS ||
          t == TK_GT || t == TK_GE || t == TK_NOT || t == TK_INSTANCEOF)
        {
          ctx.warning("bool-as-index", node->tok);
        }
      }
    }

    if (node->nodeType == PNT_BINARY_OP)
    {
      TokenType t = node->tok.type;
      if (t == TK_EQ || t == TK_NE)
      {
        Node * a = tryReplaceVar(node->children[0], true);
        Node * b = tryReplaceVar(node->children[1], true);

        TokenType left = a->tok.type;
        TokenType right = b->tok.type;
        if (left == TK_EQ || left == TK_NE || right == TK_EQ || right == TK_NE)
        {
          bool warn = true;
          if ((node->children[0]->nodeType == PNT_IDENTIFIER && nameLooksLikeResultMustBeBoolean(node->children[0]->tok.u.s)) ||
            (node->children[1]->nodeType == PNT_IDENTIFIER && nameLooksLikeResultMustBeBoolean(node->children[1]->tok.u.s)))
          {
            warn = false;
          }

          if (warn)
            ctx.warning("compared-with-bool", node->tok);
        }
      }
    }

    if (node->nodeType == PNT_WHILE_LOOP)
      if (!node->children[1] || node->children[1]->nodeType == PNT_EMPTY_STATEMENT)
        ctx.warning("empty-while-loop", node->tok);

    if (node->nodeType == PNT_FUNCTION || node->nodeType == PNT_LOCAL_FUNCTION ||
      node->nodeType == PNT_CLASS_CONSTRUCTOR || node->nodeType == PNT_CLASS_METHOD)
    {
      const char * functionName = (node->children[0] && node->children[0]->nodeType == PNT_IDENTIFIER) ?
        node->children[0]->tok.u.s : "";

      if (!functionName[0])
      {
        if (nodePath[nodePath.size() - 2])
        {
          Node * keyValue = nodePath[nodePath.size() - 2];
          if (keyValue->nodeType == PNT_KEY_VALUE || keyValue->nodeType == PNT_VAR_DECLARATOR ||
            (keyValue->nodeType == PNT_BINARY_OP && keyValue->tok.type == TK_NEWSLOT))
          {
            Node * functionNameNode = keyValue->children[0];
            if (functionNameNode && functionNameNode->nodeType == PNT_ACCESS_MEMBER)
              functionNameNode = functionNameNode->children[1];

            functionName = (functionNameNode && functionNameNode->nodeType == PNT_IDENTIFIER) ?
              functionNameNode->tok.u.s : "";
          }
        }
      }

      unsigned flags = 0;
      bool allWaysHaveReturn = findFunctionReturnTypes(node->children[2], flags);
      if (!allWaysHaveReturn)
        flags |= RT_NOTHING;

      bool warningShown = false;

      if (flags & ~(RT_BOOL | RT_UNRECOGNIZED | RT_FUNCTION_CALL))
        if (nameLooksLikeResultMustBeBoolean(functionName))
        {
          ctx.warning("named-like-return-bool", node->tok, functionName);
          warningShown = true;
        }

      if (!!(flags & RT_NOTHING) && !!(flags & (RT_NUMBER | RT_STRING | RT_TABLE | RT_ARRAY | RT_CLOSURE | RT_UNRECOGNIZED)))
      {
        ctx.warning("all-paths-return-value", node->tok);
        warningShown = true;
      }
      else if (flags)
      {
        unsigned flagsDiff = flags & ~(RT_NOTHING | RT_NULL | RT_UNRECOGNIZED | RT_FUNCTION_CALL);
        if (flagsDiff)
        {
          bool powerOfTwo = !(flagsDiff == 0) && !(flagsDiff & (flagsDiff - 1));
          if (!powerOfTwo)
          {
            ctx.warning("return-different-types", node->tok);
            warningShown = true;
          }
        }
      }

      if (!warningShown)
        if (!!(flags & RT_NOTHING) && nameLooksLikeFunctionMustReturnResult(functionName))
        {
          ctx.warning("named-like-must-return-result", node->tok, functionName);
        }

    }


    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_OR || node->tok.type == TK_AND || node->tok.type == TK_BITOR))
    {
      Node * cmp = node;
      while (cmp->children[0]->tok.type == node->tok.type && cmp->children[0]->nodeType == node->nodeType)
      {
        cmp = cmp->children[0];
        if (cmp && (isNodeEquals(node->children[1], cmp->children[1]) || isNodeEquals(node->children[1], cmp->children[0])) )
        {
          ctx.warning("copy-of-expression", cmp->children[0]->tok);
          break;
        }
      }
    }


    if (node->nodeType == PNT_FUNCTION_CALL || node->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
      checkFunctionCallFormatArguments(node);


    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_OR || node->tok.type == TK_AND))
    {
      Node * left = node->children[0];
      Node * right = node->children[1];
      if (left->nodeType == PNT_EXPRESSION_PAREN)
        left = left->children[0];
      if (right->nodeType == PNT_EXPRESSION_PAREN)
        right = right->children[0];

      left = tryReplaceVar(left, false);
      right = tryReplaceVar(right, false);

      if ((left->tok.type == TK_NE || left->tok.type == TK_EQ) && left->tok.type == right->tok.type)
      {
        TokenType boolOp = node->tok.type;
        TokenType cmpOp = left->tok.type;

        const char * constantValue = nullptr;

        if (boolOp == TK_AND && cmpOp == TK_EQ)
          constantValue = "false";

        if (boolOp == TK_OR && cmpOp == TK_NE)
          constantValue = "true";

        if (constantValue)
        {
          Node * leftConstant = left->children[1];
          Node * rightConstant = right->children[1];

          if (leftConstant->nodeType == PNT_ACCESS_MEMBER && leftConstant->children[1]->nodeType == PNT_IDENTIFIER)
            leftConstant = leftConstant->children[1];
          if (rightConstant->nodeType == PNT_ACCESS_MEMBER && rightConstant->children[1]->nodeType == PNT_IDENTIFIER)
            rightConstant = rightConstant->children[1];

          if (leftConstant->nodeType == PNT_INTEGER || leftConstant->nodeType == PNT_NULL ||
            leftConstant->nodeType == PNT_BOOL || leftConstant->nodeType == PNT_STRING ||
            leftConstant->nodeType == PNT_FLOAT || isUpperCaseIdentifier(leftConstant))
          {
            if (rightConstant->nodeType == PNT_INTEGER || rightConstant->nodeType == PNT_NULL ||
              rightConstant->nodeType == PNT_BOOL || rightConstant->nodeType == PNT_STRING ||
              rightConstant->nodeType == PNT_FLOAT || isUpperCaseIdentifier(rightConstant))
            {
              if (isNodeEquals(left->children[0], right->children[0]) && !isNodeEquals(leftConstant, rightConstant))
                ctx.warning("always-true-or-false", node->tok, constantValue);
            }
          }
        }
      }
    }


    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_AND || node->tok.type == TK_OR))
    {
      Node * leftConstant = node->children[0];
      Node * rightConstant = node->children[1];

      if (leftConstant->nodeType == PNT_EXPRESSION_PAREN)
        leftConstant = leftConstant->children[0];
      if (rightConstant->nodeType == PNT_EXPRESSION_PAREN)
        rightConstant = rightConstant->children[0];

      leftConstant = tryReplaceVar(leftConstant, false);
      rightConstant = tryReplaceVar(rightConstant, false);

      if (leftConstant->nodeType == PNT_ACCESS_MEMBER && leftConstant->children[1]->nodeType == PNT_IDENTIFIER)
        leftConstant = leftConstant->children[1];
      if (rightConstant->nodeType == PNT_ACCESS_MEMBER && rightConstant->children[1]->nodeType == PNT_IDENTIFIER)
        rightConstant = rightConstant->children[1];

      bool leftIsConstant = (leftConstant->nodeType == PNT_INTEGER || leftConstant->nodeType == PNT_NULL ||
        leftConstant->nodeType == PNT_BOOL || leftConstant->nodeType == PNT_STRING ||
        leftConstant->nodeType == PNT_FLOAT || isUpperCaseIdentifier(leftConstant));

      bool rightIsConstant = (rightConstant->nodeType == PNT_INTEGER || rightConstant->nodeType == PNT_NULL ||
        rightConstant->nodeType == PNT_BOOL || rightConstant->nodeType == PNT_STRING ||
        rightConstant->nodeType == PNT_FLOAT || isUpperCaseIdentifier(rightConstant));

      if (leftIsConstant || (rightIsConstant && node->tok.type != TK_OR))
        ctx.warning("const-in-bool-expr", node->tok);
    }


    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_DIV)
    {
      Node * leftConstant = node->children[0];
      Node * rightConstant = node->children[1];

      if (leftConstant->nodeType == PNT_EXPRESSION_PAREN)
        leftConstant = leftConstant->children[0];
      if (rightConstant->nodeType == PNT_EXPRESSION_PAREN)
        rightConstant = rightConstant->children[0];

      leftConstant = tryReplaceVar(leftConstant, false);
      rightConstant = tryReplaceVar(rightConstant, true);

      if (leftConstant->nodeType == PNT_INTEGER && rightConstant->nodeType == PNT_INTEGER)
      {
        if (rightConstant->tok.u.i == 0)
          ctx.warning("div-by-zero", node->tok);
        else if (leftConstant->tok.u.i % rightConstant->tok.u.i != 0)
          ctx.warning("round-to-int", node->tok);
      }
    }

    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_SHIFTL || node->tok.type == TK_SHIFTR || node->tok.type == TK_USHIFTR))
      if (node->children[0]->tok.type == TK_PLUS || node->children[1]->tok.type == TK_PLUS ||
        node->children[0]->tok.type == TK_MINUS || node->children[1]->tok.type == TK_MINUS ||
        node->children[0]->tok.type == TK_MUL || node->children[1]->tok.type == TK_MUL ||
        node->children[0]->tok.type == TK_DIV || node->children[1]->tok.type == TK_DIV ||
        node->children[0]->tok.type == TK_MODULO || node->children[1]->tok.type == TK_MODULO
        )
      {
        ctx.warning("shift-priority", node->tok);
      }


    if (node->nodeType == PNT_VAR_DECLARATOR && node->children.size() > 1)
    {
      Node * require = node->children[1];

      if (require->nodeType == PNT_FUNCTION_CALL)
      {
        if (require->children[0]->nodeType == PNT_IDENTIFIER && require->children.size() > 1 &&
          require->children[1]->nodeType == PNT_STRING && !strcmp(require->children[0]->tok.u.s, "require"))
        {
          const char * name = require->children[1]->tok.u.s;

          // if (variable_presense_check)
          //   moduleexports::module_export_collector(ctx, 0, name);

          if (requiredModuleNames.find(name) != requiredModuleNames.end())
            ctx.warning("already-required", require->tok, name);
          else
            requiredModuleNames.insert(name);
        }
      }
    }


    if (node->nodeType == PNT_ACCESS_MEMBER && node->children[0]->nodeType == PNT_EXPRESSION_PAREN)
    {
      if (isPotentialyNullable(node->children[0]))
        ctx.warning("access-potentially-nulled", node->tok, "expression");
    }


    if (node->nodeType == PNT_ACCESS_MEMBER && node->children[0]->nodeType == PNT_IDENTIFIER)
    {
      Node * replaced = tryReplaceVar(node->children[0], true);
      if (replaced != node->children[0] && isPotentialyNullable(replaced) && !isVariableTestedBefore(node->children[0]))
        ctx.warning("access-potentially-nulled", node->tok, node->children[0]->tok.u.s);
    }


    if (node->nodeType == PNT_FUNCTION_CALL && node->children[0]->nodeType == PNT_IDENTIFIER)
    {
      Node * replaced = tryReplaceVar(node->children[0], true);
      if (replaced != node->children[0] && isPotentialyNullable(replaced) && !isVariableTestedBefore(node->children[0]))
        ctx.warning("call-potentially-nulled", node->tok, node->children[0]->tok.u.s);
    }


    if (node->nodeType == PNT_BINARY_OP && (is_arith_op_token(node->tok.type) || is_cmp_op_token(node->tok.type)))
    {
      Node * n = nullptr;
      Node * left = node->children[0];
      Node * right = node->children[1];

      left = tryReplaceVar(left, true);
      right = tryReplaceVar(right, true);

      if (left->nodeType == PNT_FUNCTION_CALL || left->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
        n = left;
      else if (right->nodeType == PNT_FUNCTION_CALL || right->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
        n = right;

      if (n && n->children[0]->nodeType == PNT_ACCESS_MEMBER)
        n = n->children[0];

      if (n && n->children.size() > 1 && n->children[1]->nodeType == PNT_IDENTIFIER && canFunctionReturnNull(n->children[1]->tok.u.s))
        ctx.warning("func-can-return-null", node->tok, n->children[1]->tok.u.s);
    }


    if (node->nodeType == PNT_BINARY_OP && (is_cmp_op_token(node->tok.type) ||
      node->tok.type == TK_EQ || node->tok.type == TK_NE))
    {
      Node * left = node->children[0];
      Node * right = node->children[1];

      left = tryReplaceVar(left, true);
      right = tryReplaceVar(right, true);

      if (left->nodeType == PNT_TABLE_CREATION || right->nodeType == PNT_TABLE_CREATION)
        ctx.warning("cmp-with-table", node->tok);

      if (left->nodeType == PNT_ARRAY_CREATION || right->nodeType == PNT_ARRAY_CREATION)
        ctx.warning("cmp-with-array", node->tok);
    }


    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_IN)
    {
      Node * left = node->children[0];
      Node * right = node->children[1];

      left = tryReplaceVar(left, true);
      right = tryReplaceVar(right, true);

      if ((left->nodeType == PNT_UNARY_PRE_OP && left->tok.type == TK_NOT) ||
        (left->nodeType == PNT_BINARY_OP && (is_cmp_op_token(left->tok.type) ||
          left->tok.type == TK_EQ || left->tok.type == TK_NE)))
      {
        ctx.warning("bool-passed-to-in", node->tok);
      }

      if ((right->nodeType == PNT_UNARY_PRE_OP && right->tok.type == TK_NOT) ||
        (right->nodeType == PNT_BINARY_OP && (is_cmp_op_token(right->tok.type) ||
          right->tok.type == TK_EQ || right->tok.type == TK_NE)))
      {
        ctx.warning("bool-passed-to-in", node->tok);
      }
    }


    if (node->nodeType == PNT_IF_ELSE || node->nodeType == PNT_WHILE_LOOP || node->nodeType == PNT_DO_WHILE_LOOP)
      if ((node->children.size() > 1 && node->children[1] && node->children[1]->nodeType == PNT_LOCAL_VAR_DECLARATION) ||
        (node->children.size() > 2 && node->children[2] && node->children[2]->nodeType == PNT_LOCAL_VAR_DECLARATION))
      {
        ctx.warning("conditional-local-var", node->tok);
      }

    if (node->nodeType == PNT_FOR_LOOP || node->nodeType == PNT_FOR_EACH_LOOP)
      if (node->children.size() > 3 && node->children[3] && node->children[3]->nodeType == PNT_LOCAL_VAR_DECLARATION)
      {
        ctx.warning("conditional-local-var", node->tok);
      }


    if (node->nodeType == PNT_BINARY_OP && (node->tok.type == TK_PLUS || node->tok.type == TK_PLUSEQ))
    {
      Node * left = tryReplaceVar(node->children[0], true);
      Node * right = tryReplaceVar(node->children[1], true);

      if (left->nodeType == PNT_STRING || right->nodeType == PNT_STRING || isVarCanBeString(left) || isVarCanBeString(right))
        ctx.warning("plus-string", node->tok);
    }


    if (node->nodeType == PNT_SWITCH_STATEMENT)
    {
      for (size_t i = 1; i < node->children.size() - 1; i++)
      {
        Node * caseStatements = node->children[i]->children[1];

        if (caseStatements && caseStatements->children.size() == 1 && caseStatements->children[0]->nodeType == PNT_STATEMENT_LIST)
          caseStatements = caseStatements->children[0];

        if (caseStatements && caseStatements->children.size() > 0)
        {
          unsigned tmp = 0;
          bool allWaysReturnValue = findFunctionReturnTypes(caseStatements, tmp);
          if (!allWaysReturnValue)
          {
            size_t last = caseStatements->children.size() - 1;
            while (last > 0 && (!caseStatements->children[last] || caseStatements->children[last]->nodeType == PNT_EMPTY_STATEMENT))
              last--;

            if (caseStatements->children[last]->nodeType != PNT_BREAK)
              ctx.warning("missed-break", node->children[i + 1]->tok);
          }
        }
      }
    }


    const int functionComplexityThreshold = 35;

    if (node->nodeType == PNT_TABLE_CREATION || node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS ||
      node->nodeType == PNT_STATEMENT_LIST)
    {
      size_t start = (node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS) ? 3 : 0;
      for (size_t i = start; i < node->children.size(); i++)
        if (node->children[i])
        {
          Node * functionA = extractFunction(node->children[i]);
          if (functionA)
          {
            Node * bodyA = functionA->children[2];

            int complexity = getComplexity(bodyA, 0, functionComplexityThreshold); // TODO: get threshold complexity from command line args
            if (complexity >= functionComplexityThreshold)
            {
              for (size_t j = i + 1; j < node->children.size(); j++)
              {
                Node * functionB = extractFunction(node->children[j]);
                if (functionB)
                {
                  Node * bodyB = functionB->children[2];
                  int diff = getNodeDiff(bodyA, bodyB, 0, 4);
                  if (diff <= 3)
                  {
                    const char * nameA = (functionA->children[0] && functionA->children[0]->nodeType == PNT_IDENTIFIER) ?
                      functionA->children[0]->tok.u.s : "";

                    const char * nameB = (functionB->children[0] && functionB->children[0]->nodeType == PNT_IDENTIFIER) ?
                      functionB->children[0]->tok.u.s : "";

                    complexity = getComplexity(bodyA, 0, functionComplexityThreshold * 3);

                    if (diff == 0)
                      ctx.warning("duplicate-function", bodyB->tok, nameA, nameB);
                    else if (diff <= complexity / functionComplexityThreshold)
                      ctx.warning("similar-function", bodyB->tok, nameA, nameB);
                  }
                }
              }
            }
          }
        }
    }


    const int statementComplexityThreshold = 18;
    const int statementSimilarityThreshold = 25;

    if (node->nodeType == PNT_STATEMENT_LIST)
    {
      for (size_t i = 0; i < node->children.size(); i++)
        if (node->children[i])
        {
          Node * expressionA = extractAssignedExpression(node->children[i]);
          if (expressionA)
          {
            if (expressionA->nodeType == PNT_FUNCTION || expressionA->nodeType == PNT_LOCAL_FUNCTION ||
              expressionA->nodeType == PNT_LAMBDA)
            {
              continue;
            }

            int complexity = getComplexity(expressionA, 0, statementComplexityThreshold); // TODO: get threshold complexity from command line args
            if (complexity >= statementComplexityThreshold)
            {
              for (size_t j = i + 1; j < node->children.size(); j++)
              {
                Node * expressionB = extractAssignedExpression(node->children[j]);
                if (expressionB)
                {
                  int diff = getNodeDiff(expressionA, expressionB, 0, 3);
                  if (diff <= 2)
                  {
                    complexity = getComplexity(expressionA, 0, statementSimilarityThreshold * 2);

                    if (expressionA->nodeType == PNT_TABLE_CREATION || expressionA->nodeType == PNT_ARRAY_CREATION ||
                      expressionA->nodeType == PNT_FUNCTION_CALL || expressionA->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
                    {
                      complexity /= 4;
                    }

                    if (diff == 0)
                      ctx.warning("duplicate-assigned-expr", expressionB->tok);
                    else if (diff <= complexity / statementSimilarityThreshold)
                      ctx.warning("similar-assigned-expr", expressionB->tok);
                  }
                }
                else
                  break;
              }
            }
          }
        }
    }


    if ((node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NEWSLOT) || node->nodeType == PNT_KEY_VALUE ||
      node->nodeType == PNT_CLASS_MEMBER || node->nodeType == PNT_STATIC_CLASS_MEMBER)
    {
      if (node->children.size() == 2 && node->children[0] && node->children[1])
      {
        Node * function = node->children[1];
        if (function->nodeType == PNT_FUNCTION || function->nodeType == PNT_LOCAL_FUNCTION || function->nodeType == PNT_CLASS_METHOD)
        {
          Node * key = node->children[0];
          if (key->nodeType == PNT_ACCESS_MEMBER)
            key = key->children[1];

          Node * functionName = function->children[0];

          if (functionName && key && functionName->nodeType == PNT_IDENTIFIER && key->nodeType == PNT_IDENTIFIER)
          {
            const char * a = key->tok.u.s;
            const char * b = functionName->tok.u.s;
            if (strcmp(a, b) != 0)
            {
              ctx.warning("key-and-function-name", function->tok, a, b);
            }
          }
        }
      }
    }


    for (size_t i = 0; i < node->children.size(); i++)
    {
      Node * n = node->children[i];
      if (n)
      {
        if (n->nodeType == PNT_LOCAL_FUNCTION || n->nodeType == PNT_FUNCTION || n->nodeType == PNT_CLASS ||
          n->nodeType == PNT_LOCAL_CLASS)
        {
          nearest_assignments.clear();
        }

        if (n->nodeType == PNT_UNARY_PRE_OP && n->tok.type == TK_TYPEOF)
          removeNearestAssignmentsFoundAt(n->children[0]);

        if ((n->nodeType == PNT_UNARY_PRE_OP || n->nodeType == PNT_UNARY_POST_OP) &&
              (n->tok.type == TK_PLUSPLUS || n->tok.type == TK_MINUSMINUS))
        {
          if (!isVarCanBeNull(n->children[0]))
            removeNearestAssignmentsFoundAt(n->children[0]);
        }

        if (node->nodeType == PNT_TERNARY_OP && i == 0)
        {
          removeNearestAssignmentsTestNull(n);
        }

        if (n->nodeType == PNT_WHILE_LOOP || n->nodeType == PNT_DO_WHILE_LOOP)
        {
          if (n->children.size() > 0)
            removeNearestAssignmentsFoundAt(n->children[0]);
        }

        if (n->nodeType == PNT_WHILE_LOOP || n->nodeType == PNT_DO_WHILE_LOOP)
          removeNearestAssignmentsMod(n->children[1]);

        if (n->nodeType == PNT_FOR_LOOP)
        {
          removeNearestAssignmentsFoundAt(n->children[1]);
          removeNearestAssignmentsMod(n->children[3]);
        }

        if (n->nodeType == PNT_FOR_EACH_LOOP)
          removeNearestAssignmentsMod(n->children[3]);

        if (node->nodeType == PNT_IF_ELSE && i == 0)
          removeNearestAssignmentsTestNull(n);

        if (n->nodeType == PNT_BINARY_OP && n->tok.type == TK_AND)
          removeNearestAssignmentsTestNull(n->children[0]);

        if (node->nodeType == PNT_LAMBDA && i == 2)
          removeNearestAssignmentsTestNull(n);


        check(n);
        updateNearestAssignments(n);


        if (n->nodeType == PNT_BINARY_OP && (n->tok.type == TK_ASSIGN || n->tok.type == TK_PLUSEQ || n->tok.type == TK_MULEQ ||
          n->tok.type == TK_MINUSEQ || n->tok.type == TK_DIVEQ || n->tok.type == TK_NEWSLOT))
        {
          if ((!isVarCanBeNull(n->children[0]) && !isVarCanBeString(n->children[0])) ||
            n->tok.type == TK_ASSIGN || n->tok.type == TK_NEWSLOT)
          {
            removeNearestAssignmentsFoundAt(n->children[0]);
          }
        }

        if (node->nodeType == PNT_IF_ELSE)
          removeNearestAssignmentsExcludeString(node->children[i]);


        if (n->nodeType == PNT_WHILE_LOOP || n->nodeType == PNT_DO_WHILE_LOOP)
        {
          for (int j = 1; j < int(n->children.size()); j++)
            removeNearestAssignmentsFoundAt(n->children[j]);
        }

        if (n->nodeType == PNT_FUNCTION_CALL || n->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
        {
          const char * functionName = getFunctionName(n);
          if (isTestPresentInNodePath(n) || strstr(functionName, "assert") || strcmp(functionName, "type") == 0)
            for (int j = 1; j < int(n->children.size()); j++)
              removeNearestAssignmentsFoundAt(n->children[j]);
        }


        if (node->nodeType == PNT_STATEMENT_LIST)
          if (n->nodeType == PNT_LOCAL_FUNCTION || n->nodeType == PNT_FUNCTION ||
            n->nodeType == PNT_CONTINUE || n->nodeType == PNT_BREAK || n->nodeType == PNT_RETURN ||
            n->nodeType == PNT_WHILE_LOOP || n->nodeType == PNT_DO_WHILE_LOOP ||
            n->nodeType == PNT_SWITCH_STATEMENT || n->nodeType == PNT_FOR_LOOP ||
            n->nodeType == PNT_FOR_EACH_LOOP)
          {
            nearest_assignments.clear();
          }
      }
    }

    if (node->nodeType == PNT_STATEMENT_LIST)
      updateNearestAssignments(NULL);

    nodePath.pop_back();
  }


  const char * currentClass = nullptr;
  map<const char *, set<const char *> > globalTables; // name, identifiers inside
  set<const char *> globalIdentifiers;
  vector< map<const char *, IdentifierStruct> > localIdentifiers; // node, is_used


  void newIdentifier(int scope_depth, Node * var, DeclarationContext decl_context, short function_depth, bool is_module,
    bool inside_static)
  {
    if (!var || var->nodeType != PNT_IDENTIFIER)
      return;

    while (int(localIdentifiers.size()) <= scope_depth)
    {
      map<const char *, IdentifierStruct> tmp;
      localIdentifiers.push_back(tmp);
    }

    const char * name = var->tok.u.s;

    if (isStdFunction(name) && decl_context != DC_TABLE_MEMBER)
    {
      ctx.warning("ident-hides-std-function", var->tok, declContextToString(decl_context), name,
        "function from standard library");
    }

    for (int i = int(localIdentifiers.size()) - 1; i >= 0; i--)
    {
      auto it = localIdentifiers[i].find(name);
      if (it != localIdentifiers[i].end())
      {
        bool ignore = false;
        if (decl_context == DC_FUNCTION_PARAM && it->second.declContext == DC_FUNCTION_PARAM)
          ignore = true;

        if (decl_context == DC_CLASS_MEMBER && it->second.declContext == DC_CLASS_MEMBER)
          ignore = true;

        if (decl_context == DC_CLASS_MEMBER && it->second.namePtr == var->tok.u.s)
          ignore = true;

        if (decl_context == DC_TABLE_MEMBER || it->second.declContext == DC_TABLE_MEMBER)
          ignore = true;

        if (decl_context == DC_FUNCTION_PARAM &&
          nodePath[nodePath.size() - 3] && nodePath[nodePath.size() - 3]->nodeType == PNT_LAMBDA)
        {
          ignore = true;
        }

        if (inside_static && (it->second.declContext == DC_CLASS_MEMBER || it->second.declContext == DC_CLASS_METHOD))
          if (decl_context == DC_FUNCTION_PARAM || decl_context == DC_LOCAL_VARIABLE || decl_context == DC_LOOP_VARIABLE)
            ignore = true;

        if (decl_context == DC_FUNCTION_NAME &&
          nodePath[nodePath.size() - 2] && nodePath[nodePath.size() - 2]->nodeType == PNT_KEY_VALUE &&
          nodePath[nodePath.size() - 2]->children[0]->tok.u.s == var->tok.u.s)
        {
          ignore = true;
        }

        if (cmpTokenPos(it->second.declaredAt, &var->tok) >= 0 && (it->second.declContext != DC_CLASS_MEMBER &&
          it->second.declContext != DC_TABLE_MEMBER && it->second.declContext != DC_STATIC_CLASS_MEMBER))
        {
          ignore = true;
        }

        if (!ignore)
        {
          ctx.warning("ident-hides-ident", var->tok, declContextToString(decl_context), name,
            declContextToString(it->second.declContext));

          if (i == int(localIdentifiers.size()) - 1)
            return; // already defined in this scope
        }
      }
    }

    IdentifierStruct ident;
    ident.namePtr = name;
    ident.declaredAt = &var->tok;
    ident.declContext = decl_context;
    ident.declDepth = function_depth;
    ident.isModule = is_module;

    size_t i = nodePath.size();
    if (nodePath[i - 1] && nodePath[i - 1]->nodeType == PNT_FOR_EACH_LOOP)
      ident.loopNode = nodePath[i - 1];

    localIdentifiers[scope_depth].insert_or_assign(name, ident);
  }

  int cmpTokenPos(const Token * a, const Token * b) // a - b
  {
    int sa = a ? a->line * 512 + a->column : -2;
    int sb = b ? b->line * 512 + b->column : -2;
    return sa - sb;
  }

  void markIdentifierAsUsed(const char * name, const Token * tok, short function_depth)
  {
    for (int i = int(localIdentifiers.size()) - 1; i >= 0; i--)
    {
      auto it = localIdentifiers[i].find(name);
      if (it != localIdentifiers[i].end())
      {
        it->second.usedAt = tok;
        it->second.useDepth = max(it->second.useDepth, function_depth);

        if (it->second.declContext != DC_TABLE_MEMBER && it->second.declContext != DC_CLASS_MEMBER &&
          it->second.declContext != DC_STATIC_CLASS_MEMBER)
        {
          return;
        }
      }
    }
  }

  void markIdentifierAssigned(const char * name, const Token * tok, bool inside_loop, short function_depth)
  {
    for (int i = int(localIdentifiers.size()) - 1; i >= 0; i--)
    {
      auto it = localIdentifiers[i].find(name);
      if (it != localIdentifiers[i].end())
      {
        IdentifierStruct & ident = it->second;
        ident.assignedAt = tok;
        ident.assignedInsideLoop = inside_loop;
        ident.assignDepth = max(ident.assignDepth, function_depth);
        if (ident.declContext == DC_CLASS_NAME || ident.declContext == DC_FUNCTION_NAME)
          ctx.warning("trying-to-modify", *tok, declContextToString(ident.declContext), name);
        return;
      }
    }
  }

  const IdentifierStruct * getIdentifierStructPtr(const char * name)
  {
    for (int i = int(localIdentifiers.size()) - 1; i >= 0; i--)
    {
      auto it = localIdentifiers[i].find(name);
      if (it != localIdentifiers[i].end())
        return &(it->second);
    }
    return nullptr;
  }

  DeclarationContext getIdentifiedDeclarationContext(const char * parent, const char * child, int from_scope)
  {
    for (int i = std::min(int(localIdentifiers.size()) - 1, from_scope); i >= 0; i--)
    {
      auto it = localIdentifiers[i].find(parent);
      if (it != localIdentifiers[i].end())
      {
        if (it->second.declContext == DC_TABLE_MEMBER || it->second.declContext == DC_CLASS_MEMBER)
          if (i == from_scope)
            continue;

        return it->second.declContext;
      }
    }

    if (moduleexports::is_identifier_present_in_root(parent))
      return DC_GLOBAL_VARIABLE;

    if (trusted::trusted_identifiers)
    {
      trusted::TrustedContext res = trusted::find(string(parent), string(child));
      if (res == trusted::TR_CHILD_NOT_FOUND)
        return DC_CHILD_NOT_FOUND;
      else if (res == trusted::TR_CONST)
        return DC_CONSTANT;
      else if (res == trusted::TR_LOCAL)
        return DC_LOCAL_VARIABLE;
      else if (res == trusted::TR_GLOBAL)
        return DC_GLOBAL_VARIABLE;
    }


    const char * currentClass = nullptr;
    for (size_t i = nodePath.size() - 1; nodePath[i] != nullptr; i--)
      if (nodePath[i]->nodeType == PNT_FUNCTION && nodePath[i]->children[0] &&
        nodePath[i]->children[0]->nodeType == PNT_BINARY_OP &&
        nodePath[i]->children[0]->tok.type == TK_DOUBLE_COLON && nodePath[i]->children[0]->children[0]->nodeType == PNT_IDENTIFIER)
      {
        currentClass = nodePath[i]->children[0]->children[0]->tok.u.s;
        break;
      }

    auto it = globalTables.find(currentClass);
    if (it != globalTables.end())
      if (it->second.find(parent) != it->second.end())
        return DC_CLASS_MEMBER;

    if (globalIdentifiers.find(parent) != globalIdentifiers.end())
      return DC_GLOBAL_VARIABLE;

    if (is_ident_visible(parent, nodePath))
      return DC_IDENTIFIER;

    return DC_NONE;
  }

  void leaveScope(int scope_depth)
  {
    while (!localIdentifiers.empty() && int(localIdentifiers.size()) > scope_depth)
    {
      for (auto & it : localIdentifiers.back())
      {
        IdentifierStruct & ident = it.second;
        if (!ident.usedAt && ident.declaredAt)
          if (ident.declContext == DC_LOOP_VARIABLE)
          {
            bool ignore = false;

            if (ident.loopNode)
              for (auto & it2 : localIdentifiers.back())
                if (&it != &it2 && ident.loopNode == it2.second.loopNode && it2.second.usedAt)
                {
                  ignore = true; // other variable of this loop is used
                  break;
                 }

            if (!ignore)
              ctx.warning("declared-never-used", *ident.declaredAt, declContextToString(ident.declContext), ident.namePtr);
          }
      }

      for (auto & it : localIdentifiers.back())
      {
        IdentifierStruct & ident = it.second;
        if (!ident.usedAt && ident.declaredAt)
          if (ident.declContext == DC_LOCAL_VARIABLE || ident.declContext == DC_ENUM_NAME ||
            ident.declContext == DC_GLOBAL_ENUM_NAME || ident.declContext == DC_LOCAL_FUNCTION_NAME)
          {
            ctx.warning("declared-never-used", *ident.declaredAt, declContextToString(ident.declContext), ident.namePtr);
          }

        if (ident.assignedAt && cmpTokenPos(ident.usedAt, ident.assignedAt) < 0 && !ident.assignedInsideLoop &&
          ident.useDepth == ident.assignDepth && ident.useDepth == ident.declDepth)
        {
          if (ident.declContext == DC_LOCAL_VARIABLE || ident.declContext == DC_FUNCTION_PARAM)
            ctx.warning("assigned-never-used", *ident.assignedAt, declContextToString(ident.declContext), ident.namePtr);
        }
      }

      localIdentifiers.pop_back();
    }
  }


  void checkDeclared(Node * node, Node * child_node, bool inside_static, int from_scope)
  {
    if (!node || node->nodeType != PNT_IDENTIFIER)
      return;

    const char * childName = "";
    if (child_node && child_node->nodeType == PNT_IDENTIFIER)
      childName = child_node->tok.u.s;

    DeclarationContext dc = getIdentifiedDeclarationContext(node->tok.u.s, childName, from_scope);
    if (child_node && dc == DC_CHILD_NOT_FOUND)
      ctx.warning("unknown-identifier", child_node->tok, child_node->tok.u.s);

    if (dc == DC_NONE && mustTestForDeclared(node))
    {
      if (isUpperCaseIdentifier(node))
      {
        if (!ctx.isWarningSuppressed("undefined-const"))
        {
          ctx.warning("undefined-const", node->tok, node->tok.u.s);
        }
        else if (!ctx.isWarningSuppressed("const-never-declared") &&
          ever_declared.find(std::string(node->tok.u.s)) == ever_declared.end())
        {
          ctx.warning("const-never-declared", node->tok, node->tok.u.s);
        }
      }
      else
      {
        if (!ctx.isWarningSuppressed("undefined-variable"))
          ctx.warning("undefined-variable", node->tok, node->tok.u.s);
        else if (ever_declared.find(std::string(node->tok.u.s)) == ever_declared.end())
          ctx.warning("never-declared", node->tok, node->tok.u.s);
      }
    }

    if (inside_static && (dc == DC_CLASS_MEMBER || dc == DC_CLASS_METHOD))
      ctx.warning("used-from-static", node->tok, node->tok.u.s);
  }


  bool is_function_calls_lamda_inplace(const char * name)
  {
    return (
      !strcmp(name, "findvalue") ||
      !strcmp(name, "findindex") ||
      !strcmp(name, "update") ||
      !strcmp(name, "search") ||
      !strcmp(name, "filter") ||
      !strcmp(name, "map") ||
      !strcmp(name, "reduce") ||
      !strcmp(name, "each") ||
      !strcmp(name, "sort") ||
      !strcmp(name, "assert") ||
      !strcmp(name, "combine") ||
      !strcmp(name, "persist") ||
      !strcmp(name, "sharedWatched") ||
      !strcmp(name, "join")
      );
  }


  void checkVariables(Node * node, int scope_depth, int line_of_next_token, bool dont_mark_used, bool inside_lambda,
    bool inside_loop, bool inside_access_member, int function_depth, bool inside_static)
  {
    nodePath.push_back(node);

    if (node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS)
      inside_static = false;

    if (node->nodeType == PNT_STATIC_CLASS_MEMBER)
      inside_static = true;

    //if (node->tok.type != TK_INTEGER && node->tok.type != TK_FLOAT)
    //  fprintf(out_stream, "CV: %d: %s\n", scope_depth, node->tok.u.s);

    // used identifiers
    if (node->nodeType == PNT_IDENTIFIER && !dont_mark_used)
      markIdentifierAsUsed(node->tok.u.s, &node->tok, function_depth);


    if (node->nodeType == PNT_IDENTIFIER && !dont_mark_used && !inside_access_member)
    {
      const IdentifierStruct * ident = getIdentifierStructPtr(node->tok.u.s);
      if (ident && ident->declContext == DC_LOOP_VARIABLE)
      {
        for (size_t i = nodePath.size() - 2; i > 0; i--)
        {
          Node * n = nodePath[i];
          if (!n)
            break;

          if (n->tok.line <= ident->declaredAt->line)
            break;

          if (n->nodeType == PNT_FUNCTION || n->nodeType == PNT_LOCAL_FUNCTION || n->nodeType == PNT_LAMBDA)
          {
            Node * prevNode = nodePath[i - 1];
            if (prevNode)
              if (prevNode->nodeType == PNT_FUNCTION_CALL || prevNode->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
              {
                const char * name = getFunctionName(prevNode);
                if (is_function_calls_lamda_inplace(name))
                  continue;
              }

            ctx.warning("iterator-in-lambda", node->tok, node->tok.u.s);
            break;
          }
        }
      }
    }


    if (!inside_access_member)
    {
      if (node->nodeType == PNT_RETURN || node->nodeType == PNT_UNARY_PRE_OP || node->nodeType == PNT_UNARY_POST_OP ||
        node->nodeType == PNT_YIELD ||
        node->nodeType == PNT_ACCESS_MEMBER || node->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL ||
        node->nodeType == PNT_ACCESS_CONSTRUCTOR || node->nodeType == PNT_EXPRESSION_PAREN ||
        node->nodeType == PNT_SWITCH_STATEMENT || node->nodeType == PNT_IF_ELSE || node->nodeType == PNT_SWITCH_CASE)
      {
        Node * test = node->children.size() > 0 ? node->children[0] : nullptr;
        checkDeclared(test, node->nodeType == PNT_ACCESS_MEMBER ? node->children[1] : nullptr, inside_static, scope_depth);
      }
      else if (node->nodeType == PNT_VAR_DECLARATOR)
      {
        Node * test = node->children.size() > 1 ? node->children[1] : nullptr;
        checkDeclared(test, nullptr, inside_static, scope_depth);
      }
      else if (node->nodeType == PNT_FOR_EACH_LOOP)
      {
        Node * test = node->children.size() > 2 ? node->children[2] : nullptr;
        checkDeclared(test, nullptr, inside_static, scope_depth);
      }
      else if (node->nodeType == PNT_KEY_VALUE ||
        node->nodeType == PNT_STATIC_CLASS_MEMBER || node->nodeType == PNT_CLASS_MEMBER)
      {
        Node * test = node->children.size() > 1 ? node->children[1] : nullptr;
        checkDeclared(test, nullptr, inside_static, scope_depth - 1);
      }
      else if (node->nodeType == PNT_TERNARY_OP || node->nodeType == PNT_ARRAY_CREATION ||
        node->nodeType == PNT_FUNCTION_CALL || node->nodeType == PNT_FUNCTION_CALL_IF_NOT_NULL)
      {
        for (size_t i = 0; i < node->children.size(); i++)
        {
          Node * test = node->children[i];
          checkDeclared(test, nullptr, inside_static, scope_depth);
        }
      }
      else if (node->nodeType == PNT_BINARY_OP && node->tok.type != TK_DOUBLE_COLON)
      {
        size_t from = 0;
        if (node->tok.type == TK_NEWSLOT)
          from = 1;

        for (size_t i = from; i < node->children.size(); i++)
        {
          Node * test = node->children[i];
          checkDeclared(test, nullptr, inside_static, scope_depth);
        }
      }
    }


    if (node->nodeType == PNT_BINARY_OP &&
      (node->tok.type == TK_ASSIGN || node->tok.type == TK_PLUSEQ || node->tok.type == TK_MINUSEQ ||
        node->tok.type == TK_MULEQ || node->tok.type == TK_DIVEQ || node->tok.type == TK_MODEQ))
    {
      if (node->children[0]->nodeType == PNT_IDENTIFIER)
      {
        const char * name = node->children[0]->tok.u.s;
        markIdentifierAssigned(name, &node->tok, inside_loop, function_depth);
      }
    }


    if (node->nodeType == PNT_FOR_LOOP || node->nodeType == PNT_FOR_EACH_LOOP || node->nodeType == PNT_WHILE_LOOP ||
      node->nodeType == PNT_DO_WHILE_LOOP)
    {
      inside_loop = true;
    }

    if (node->nodeType == PNT_FUNCTION || node->nodeType == PNT_CLASS_CONSTRUCTOR || node->nodeType == PNT_LOCAL_FUNCTION ||
      node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS || node->nodeType == PNT_CLASS_MEMBER ||
      node->nodeType == PNT_CLASS_METHOD)
    {
      inside_loop = false;
    }

    if (node->nodeType == PNT_FUNCTION || node->nodeType == PNT_CLASS_CONSTRUCTOR || node->nodeType == PNT_LOCAL_FUNCTION ||
      node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS || node->nodeType == PNT_CLASS_MEMBER ||
      node->nodeType == PNT_CLASS_METHOD || node->nodeType == PNT_LAMBDA || node->nodeType == PNT_TABLE_CREATION)
    {
      function_depth++;
    }

    bool newScope = (node->nodeType == PNT_STATEMENT_LIST ||
      node->nodeType == PNT_FOR_LOOP || node->nodeType == PNT_FOR_EACH_LOOP || node->nodeType == PNT_CLASS ||
      node->nodeType == PNT_LOCAL_CLASS ||
      node->nodeType == PNT_LAMBDA || node->nodeType == PNT_FUNCTION || node->nodeType == PNT_LOCAL_FUNCTION ||
      node->nodeType == PNT_CLASS_CONSTRUCTOR || node->nodeType == PNT_CLASS_METHOD || node->nodeType == PNT_TABLE_CREATION ||
      node->nodeType == PNT_TRY_CATCH);


    bool isModule = false;
    Node * var = nullptr;
    Node * var2 = nullptr; // for index of foreach
    DeclarationContext declContext = DC_NONE;
    if (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NEWSLOT)
    {
      declContext = DC_GLOBAL_VARIABLE;
      var = node->children[0];
      if (var->nodeType == PNT_ACCESS_MEMBER && var->tok.type == TK_DOUBLE_COLON)
        var = var->children[1];
    }
    else if (node->nodeType == PNT_CLASS || node->nodeType == PNT_LOCAL_CLASS)
    {
      if (node->children[0])
      {
        declContext = DC_CLASS_NAME;
        var = node->children[0];
      }

      for (size_t i = 3; i < node->children.size(); i++)
      {
        Node * member = node->children[i];
        if (member->nodeType == PNT_CLASS_MEMBER || member->nodeType == PNT_STATIC_CLASS_MEMBER)
        {
          newIdentifier(scope_depth + 1, member->children[0],
            member->nodeType == PNT_STATIC_CLASS_MEMBER ? DC_STATIC_CLASS_MEMBER : DC_CLASS_MEMBER, function_depth, false,
            inside_static);
        }
      }
    }
    else if (node->nodeType == PNT_TABLE_CREATION)
    {
      for (size_t i = 0; i < node->children.size(); i++)
      {
        Node * keyvalue = node->children[i];
        if (keyvalue->nodeType == PNT_KEY_VALUE)
        {
          bool ignore = (keyvalue->children.size() > 1 && isNodeEquals(keyvalue->children[0], keyvalue->children[1]));
          if (!ignore)
            newIdentifier(scope_depth + 1, keyvalue->children[0], DC_TABLE_MEMBER, function_depth, false,
              inside_static);
        }
      }
    }
    else if (node->nodeType == PNT_VAR_DECLARATOR)
    {
      declContext = DC_LOCAL_VARIABLE;
      var = node->children[0];

      if (node->children.size() > 1 && node->children[1]->nodeType == PNT_FUNCTION_CALL &&
        node->children[1]->children[0]->nodeType == PNT_IDENTIFIER)
      {
        const char * name = node->children[1]->children[0]->tok.u.s;
        if (name && (!strcmp(name, "require") || !strcmp(name, "require_optional")))
          isModule = true;
      }
    }
    else if (node->nodeType == PNT_FUNCTION_PARAMETER)
    {
      declContext = DC_FUNCTION_PARAM;
      var = node->children[0];
    }
    else if (node->nodeType == PNT_FUNCTION)
    {
      declContext = DC_FUNCTION_NAME;
      var = node->children[0];
    }
    else if (node->nodeType == PNT_LOCAL_FUNCTION)
    {
      declContext = DC_LOCAL_FUNCTION_NAME;
      var = node->children[0];
    }
    else if (node->nodeType == PNT_FOR_EACH_LOOP)
    {
      declContext = DC_LOOP_VARIABLE;
      var = node->children[0];
      var2 = node->children[1];
    }
    else if (node->nodeType == PNT_CONST_DECLARATION)
    {
      declContext = DC_CONSTANT;
      var = node->children[0];
    }
    else if (node->nodeType == PNT_GLOBAL_CONST_DECLARATION)
    {
      declContext = DC_GLOBAL_CONSTANT;
      var = node->children[0];
    }
    else if (node->nodeType == PNT_ENUM)
    {
      declContext = DC_ENUM_NAME;
      var = node->children[0];
    }
    else if (node->nodeType == PNT_GLOBAL_ENUM)
    {
      declContext = DC_GLOBAL_ENUM_NAME;
      var = node->children[0];
    }
    else if (node->nodeType == PNT_TRY_CATCH)
    {
      declContext = DC_LOCAL_VARIABLE;
      var = node->children[1];
    }

    int nextScope = newScope ? scope_depth + 1 : scope_depth;
    int curScope = (node->nodeType == PNT_FOR_LOOP || node->nodeType == PNT_FOR_EACH_LOOP || node->nodeType == PNT_TRY_CATCH) ?
      scope_depth + 1 : scope_depth;

    bool reverseVisit = (node->nodeType == PNT_VAR_DECLARATOR || node->nodeType == PNT_KEY_VALUE ||
      (node->nodeType == PNT_BINARY_OP && node->tok.type == TK_NEWSLOT));

    if (!reverseVisit)
    {
      if (var)
        newIdentifier(curScope, var, declContext, function_depth, isModule, inside_static);
      if (var2)
        newIdentifier(curScope, var2, declContext, function_depth, isModule, inside_static);
    }

    int fromChild = 0;
    int toChild = int(node->children.size()) - 1;
    int loopDir = 1;


    for (size_t i = fromChild; i != toChild + loopDir; i += loopDir)
      if (node->children[i])
      {
        bool dontMarkUsed = false;
        if ((node->nodeType == PNT_VAR_DECLARATOR && i == 0) ||
          (node->nodeType == PNT_FOR_EACH_LOOP && i <= 1) ||
          (node->nodeType == PNT_FUNCTION_PARAMETER && i == 0) ||
          (node->nodeType == PNT_LOCAL_FUNCTION && i == 0) ||
          (node->nodeType == PNT_KEY_VALUE && i == 0))
        {
          dontMarkUsed = true;
        }

        bool accessMember = i > 0 && (node->nodeType == PNT_ACCESS_MEMBER || node->nodeType == PNT_ACCESS_MEMBER_IF_NOT_NULL) &&
          (node->tok.type != TK_LSQUARE && node->tok.type != TK_NULLGETOBJ);

        if (node->nodeType == PNT_LAMBDA)
          inside_lambda = true;

        size_t nextIndex = i + 1;
        while (nextIndex < node->children.size() && !node->children[nextIndex])
          nextIndex++;

        int lineOfNextToken = (nextIndex < node->children.size()) ? node->children[nextIndex]->tok.line : line_of_next_token;
        checkVariables(node->children[i], nextScope, lineOfNextToken, dontMarkUsed, inside_lambda, inside_loop,
          accessMember, function_depth, inside_static);
      }


    if (reverseVisit)
    {
      if (var)
        newIdentifier(curScope, var, declContext, function_depth, isModule, inside_static);
      if (var2)
        newIdentifier(curScope, var2, declContext, function_depth, isModule, inside_static);
    }

    if (newScope)
      leaveScope(scope_depth + 1);

    nodePath.pop_back();
  }


  void collectGlobalTables(Node * root)
  {
    if (!root || root->nodeType != PNT_STATEMENT_LIST)
      return;

    for (size_t i = 0; i < root->children.size(); i++)
    {
      Node * child = root->children[i];
      if (!child)
        continue;

      if (child->nodeType == PNT_BINARY_OP && child->tok.type == TK_NEWSLOT)
      {
        const char * slotName = nullptr;
        if (child->children[0]->nodeType == PNT_IDENTIFIER)
          slotName = child->children[0]->tok.u.s;

        if (child->children[0]->nodeType == PNT_ACCESS_MEMBER && child->children[0]->children[0]->nodeType == PNT_ROOT &&
          child->children[0]->children[1]->nodeType == PNT_IDENTIFIER)
        {
          slotName = child->children[0]->children[1]->tok.u.s;
        }

        if (slotName)
        {
          set<const char *> itemNames;
          if (child->children[1]->nodeType == PNT_TABLE_CREATION)
          {
            Node * tableNode = child->children[1];
            for (size_t j = 0; j < tableNode->children.size(); j++)
              if (tableNode->children[j]->children[0]->nodeType == PNT_IDENTIFIER)
                itemNames.insert(tableNode->children[j]->children[0]->tok.u.s);
          }
          else if (child->children[1]->nodeType == PNT_CLASS || child->children[1]->nodeType == PNT_LOCAL_CLASS)
          {
            Node * classNode = child->children[1];
            for (size_t j = 3; j < classNode->children.size(); j++)
              if (classNode->children[j]->children[0] && classNode->children[j]->children[0]->nodeType == PNT_IDENTIFIER)
                itemNames.insert(classNode->children[j]->children[0]->tok.u.s);
          }

          auto it = globalTables.find(slotName);
          if (it == globalTables.end())
            globalTables.insert(make_pair(slotName, itemNames));
          else
            globalTables[slotName] = itemNames;
        }
      }
      else if (child->nodeType == PNT_CLASS || child->nodeType == PNT_LOCAL_CLASS)
      {
        const char * slotName =
          (child->children[0] && child->children[0]->nodeType == PNT_IDENTIFIER) ? child->children[0]->tok.u.s : nullptr;

        if (slotName)
        {
          set<const char *> itemNames;
          for (size_t j = 3; j < child->children.size(); j++)
            if (child->children[j]->children[0] && child->children[j]->children[0]->nodeType == PNT_IDENTIFIER)
              itemNames.insert(child->children[j]->children[0]->tok.u.s);

          globalTables.insert(make_pair(slotName, itemNames));
        }
      }

      if ((child->nodeType == PNT_FUNCTION || child->nodeType == PNT_LOCAL_FUNCTION) && child->children[0])
      {
        if (child->children[0]->nodeType == PNT_IDENTIFIER)
        {
          globalIdentifiers.insert(child->children[0]->tok.u.s);
        }

        if (child->children[0]->nodeType == PNT_BINARY_OP && child->children[0]->tok.type == TK_DOUBLE_COLON)
          if (child->children[0]->children[0]->nodeType == PNT_IDENTIFIER && child->children[0]->children[1]->nodeType == PNT_IDENTIFIER)
          {
            const char * className = child->children[0]->children[0]->tok.u.s;
            const char * functionName = child->children[0]->children[1]->tok.u.s;
            auto it = globalTables.find(className);
            if (it == globalTables.end())
            {
              set<const char *> tmp;
              tmp.insert(functionName);
              globalTables.insert(make_pair(className, tmp));
            }
            else
              it->second.insert(functionName);
          }
      }
    }
  }

};


void print_usage()
{
  fprintf(out_stream, "\nUsage:\n");
  fprintf(out_stream, "  quirrel_static_analyzer [-wNNN] <file_name.nut>\n");
  fprintf(out_stream, "  or\n");
  fprintf(out_stream, "  quirrel_static_analyzer [-wNNN] --files:<files-list.txt>\n\n");
  fprintf(out_stream, "  --files:<files-list.txt> - process multiple files. <files-list.txt> contains file names, one name per line.\n");
  fprintf(out_stream, "  --predefinition-files:<files-list.txt> - this list used to collect defined classed and tables.\n");
  fprintf(out_stream, "  --output:<output-file.txt> - write output to <output-file.txt> instead of stdout.\n");
  fprintf(out_stream, "  --output-mode:<1-line | 2-lines | full>  default is 'full'.\n");
  fprintf(out_stream, "  --csq-exe:<csq.exe with path> - set path to console squirrel executable file.\n");
  fprintf(out_stream, "  --warnings-list - show all supported warnings.\n");
  fprintf(out_stream, "  --inverse-warnings - all warnings will be disabled by default, -wNNN will enable warning.\n");
  fprintf(out_stream, "  -wNNN - this type of warnings will be ignored.\n");
  fprintf(out_stream, "  To suppress warning for the whole file add comment '//-file:wNNN' (NNN is warning number) or '//-file:warning-text-id'.\n");
  fprintf(out_stream, "  To suppress any single warning add comment '//-wNNN' to the end of line (NNN is warning number) or '//-warning-text-id'.\n\n");
}


OutputMode str_to_output_mode(const char * str)
{
  if (!strcmp(str, "1-line"))
    return OM_1_LINE;
  else if (!strcmp(str, "2-lines"))
    return OM_2_LINES;
  else if (!strcmp(str, "full"))
    return OM_FULL;

  static bool errorShown = false;
  if (!errorShown)
    fprintf(out_stream, "WARNING: invalid output mode '%s', 'full' mode will be used.\n", str);
  errorShown = true;

  return OM_FULL;
}

static int argc__ = 0;
static char ** argv__ = nullptr;

int process_single_source(const string & file_name, const string & source_code, bool use_csq, bool collect_ident_tree)
{
  CompilationContext ctx;

  if (collect_ident_tree)
    use_csq = false;

  bool inverseWarnings = false;
  bool printAst = false;

  for (int i = 1; i < argc__; i++)
  {
    const char * arg = argv__[i];

    {
      // HACK: fix "duplucate-if-expression" -> "duplicate-if-expression", and support old config files
      if (!strcmp("-duplucate-if-expression", arg))
        arg = "-duplicate-if-expression";
    }


    if (!strcmp(arg, "--inverse-warnings"))
      inverseWarnings = true;
    if (!strncmp(arg, "--csq-exe:", 10))
      moduleexports::csq_exe = arg + 10;
    if (!strcmp(arg, "--print-ast"))
      printAst = true;
    if (!strncmp(arg, "--output-mode:", 14))
      ctx.outputMode = str_to_output_mode(arg + 14);
    else if (arg[0] == '-' && (toupper(arg[1]) == 'W') && isdigit(arg[2]))
      ctx.suppressWaring(atoi(arg + 2));
    else if (arg[0] == '-' && isalpha(arg[1]))
      ctx.suppressWaring(arg + 1);
  }

  if (inverseWarnings)
    ctx.inverseWarningsSuppression();

  variable_presense_check = (!ctx.isWarningSuppressed("undefined-variable") ||
    !ctx.isWarningSuppressed("never-declared")) && use_csq;

  int expectWarningNumber = 0;
  bool expectError = false;


  if (file_name.empty())
  {
    fprintf(out_stream, "ERROR: (2) Expected file name");
    return 1;
  }

  if (source_code.empty())
  {
    ifstream tmp(file_name);
    if (tmp.fail())
    {
      fprintf(out_stream, "ERROR: Cannot open file '%s'\n", file_name.c_str());
      return 1;
    }
    ctx.code = string((std::istreambuf_iterator<char>(tmp)), std::istreambuf_iterator<char>());
  }
  else
  {
    ctx.code = source_code;
  }

  ctx.setFileName(file_name);

  if (variable_presense_check)
    moduleexports::module_export_collector(ctx, 0, 0, nullptr);


  if (!strncmp(ctx.code.c_str(), "//expect:error", sizeof("//expect:error") - 1))
    expectError = true;

  if (!strncmp(ctx.code.c_str(), "//expect:w", sizeof("//expect:w") - 1))
    expectWarningNumber = atoi(ctx.code.c_str() + sizeof("//expect:w") - 1);

  if (expectError || expectWarningNumber)
    ctx.clearSuppressedWarnings();

  Lexer lex(ctx);

  bool res = true;
  res = res && lex.process();
  if (res)
  {
    Node * root = sq3_parse(lex); // do not delete, will be destroyed in ~CompilationContext()

    if (root && printAst)
      root->print();


    if (!ctx.isError)
    {
      if (collect_ident_tree)
      {
        if (root)
        {
          collect_ever_declared(lex);
          global_collect_tree(root, &ident_root);
          return 0;
        }
      }
      else
      {
        Analyzer analyzer(lex);

        if (root)
        {
          collect_ever_declared(lex);
          analyzer.collectGlobalTables(root);
          analyzer.check(root);
          analyzer.checkVariables(root, 0, INT_MAX / 2, false, false, false, false, 1, false);
        }
      }
    }
  }

  if (ctx.isError || ctx.isWarning)
    res = false;

  if (expectError && !ctx.isError)
  {
    fprintf(out_stream, "Expected error.\n");
    return 1;
  }

  if (expectWarningNumber && (!ctx.isWarning || ctx.shownWarningsAndErrors.size() != 1 ||
    ctx.shownWarningsAndErrors[0] != expectWarningNumber))
  {
    fprintf(out_stream, "Expected only one warning 'w%d'.\n", expectWarningNumber);
    return 1;
  }

  if (expectError || expectWarningNumber)
    return 0;

  return res ? 0 : 1;
}


const char * next_string(const char * p, string & out_str)
{
  out_str.clear();
  out_str.reserve(100);
  if (*p == 0x0d)
    p++;
  if (*p == 0x0a)
    p++;

  while (*p)
  {
    if (*p == 0x0d || *p == 0x0a)
      break;

    out_str += *p;
    p++;
  }
  return p;
}

int process_stream_file(const char * stream_file_name)
{
  ifstream tmp(stream_file_name);
  if (tmp.fail())
  {
    fprintf(out_stream, "ERROR: Cannot open stream file '%s'\n", stream_file_name);
    return 1;
  }

  string stream((std::istreambuf_iterator<char>(tmp)), std::istreambuf_iterator<char>());
  if (stream.empty())
  {
    fprintf(out_stream, "ERROR: Stream file is empty '%s'\n", stream_file_name);
    return 1;
  }

  int res = 0;
  const char * p = stream.c_str();

  string fileName;
  trusted::TrustedContext trustedContext = trusted::TR_CONST;
  string code;
  bool insideCode = false;

  for (;;)
  {
    string buf;
    p = next_string(p, buf);

    if (insideCode)
    {
      if (buf[0] != '#' || buf[1] != '#')
      {
        code += buf;
        code += "\n";
      }

      if ((buf[0] == '#' && buf[1] == '#') || !*p) // end of code
      {
        res |= process_single_source(fileName, code, false, false);
        insideCode = false;
      }
    }

    if (!*p)
      break;

    if (!strncmp(buf.c_str(), "###[FILE_NAME]", sizeof("###[FILE_NAME]") - 1))
    {
      fileName = string(buf.c_str() + sizeof("###[FILE_NAME]") - 1);
      trusted::clear();
      code.clear();
      insideCode = false;
    }
    else if (!strcmp(buf.c_str(), "###[LOCALS]"))
      trustedContext = trusted::TR_LOCAL;
    else if (!strcmp(buf.c_str(), "###[GLOBALS]"))
      trustedContext = trusted::TR_GLOBAL;
    else if (!strcmp(buf.c_str(), "###[CONSTANTS]"))
      trustedContext = trusted::TR_CONST;
    else if (!strcmp(buf.c_str(), "###[CODE]"))
    {
      insideCode = true;
    }
    else if (!buf.empty() && !insideCode)
    {
      const char * dot = strchr(buf.c_str(), '.');
      string parent(buf.c_str(), dot ? dot - buf.c_str() : buf.length());
      string child;
      if (dot)
        child = string(dot + 1);

      trusted::add(trustedContext, parent, child);
    }
  }

  return res;
}


int main(int argc, char ** argv)
{
  argv__ = argv;
  argc__ = argc;

  if (argc <= 1 || !strcmp(argv[1], "--help"))
  {
    print_usage();
    return 0;
  }


  for (int i = 1; i < argc; i++)
  {
    const char * arg = argv[i];
    if (!strncmp(arg, "--output:", 9))
    {
      const char * outFileName = arg + 9;
      FILE * fo = fopen(outFileName, "wt");
      if (!fo)
      {
        fprintf(out_stream, "ERROR: cannot open file '%s' for write.\n", outFileName);
        return 1;
      }
      else
      {
        out_stream = fo;
      }
    }
  }

  if (argc >= 2 && !strcmp(argv[1], "--warnings-list"))
  {
    CompilationContext::printAllWarningsList();
    return 0;
  }

  const char * streamFile = nullptr;
  vector <string> fileList;
  vector <string> predefinitionFileList;

  for (int i = 1; i < argc; i++)
  {
    const char * arg = argv[i];
    if (arg[0] != '-')
    {
      fileList.push_back(string(arg));
      break;
    }

    if (!strncmp(arg, "--stream:", 9))
      streamFile = arg + 9;

    bool isFiles = !strncmp(arg, "--files:", 8);
    bool isPredefinitionFiles = !strncmp(arg, "--predefinition-files:", 22);
    if (isPredefinitionFiles)
      two_pass_scan = true;

    if (isFiles || isPredefinitionFiles)
    {
      const char * fn = arg + (isPredefinitionFiles ? 22 : 8);
      ifstream tmp(fn);
      if (tmp.fail())
      {
        fprintf(out_stream, "ERROR: Cannot open files list '%s'\n", fn);
        return 1;
      }

      string filesListString((std::istreambuf_iterator<char>(tmp)), std::istreambuf_iterator<char>());
      filesListString += " ";
      string nutName;
      for (size_t j = 0; j < filesListString.size(); j++)
      {
        if (filesListString[j] > ' ')
          nutName += filesListString[j];
        else if (!nutName.empty())
        {
          if (isPredefinitionFiles)
            predefinitionFileList.push_back(nutName);
          else
            fileList.push_back(nutName);
          nutName.clear();
        }
      }
    }
  }


  string sourceCode;

  int res = 0;

  if (streamFile)
  {
    res = process_stream_file(streamFile);
  }
  else
  {
    if (fileList.empty())
    {
      fprintf(out_stream, "ERROR: (2) Expected file name");
      return 1;
    }

    if (two_pass_scan)
    {
      for (string & fileName : predefinitionFileList)
        res |= process_single_source(fileName, sourceCode, true, true);

      //dump_ident_root(0, &ident_root);
    }

    for (string & fileName : fileList)
      res |= process_single_source(fileName, sourceCode, true, false);
  }

  return res;
}

