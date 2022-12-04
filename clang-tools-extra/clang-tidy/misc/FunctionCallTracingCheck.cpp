//===--- FunctionCallTracingCheck.cpp - clang-tidy ------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "FunctionCallTracingCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/OperationKinds.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Tooling/Transformer/RangeSelector.h" // node("hoge"), name("hoge")
#include "clang/Tooling/Transformer/RewriteRule.h" // changeTo(), addInclude()
#include "clang/Tooling/Transformer/Stencil.h"
#include "llvm/ADT/StringRef.h"

#include <iostream>

using namespace clang::ast_matchers;

#define STARTSWITH(str, x) (str.find(x) == 0)

namespace clang {
namespace ast_matchers {

AST_MATCHER(Expr, isInMacro) {
  return Node.getBeginLoc().isMacroID();
}

AST_MATCHER(CallExpr, returnsVoid) {
  return Node.getCallReturnType(Finder->getASTContext())->isVoidType();
}

AST_MATCHER(FunctionDecl, isBuiltinFunction) {
  auto name = Node.getNameInfo().getName().getAsString();
  return STARTSWITH(name, "__builtin_") || STARTSWITH(name, "__atomic_") || STARTSWITH(name, "__c11_atomic_");
}

AST_MATCHER_P(DeclRefExpr, hasNameStartsWith, std::string, value) {
  std::cerr << "[*] hasNameStartsWith: " << Node.getNameInfo().getName().getAsString() << std::endl;
  return STARTSWITH(Node.getNameInfo().getName().getAsString(), value);
}

// AST_MATCHER(Expr, isFirstChildren) {
//   const ASTContext &Context = Finder->getASTContext();
//   auto Parents = Context.getParents(Node);
//   if (Parents.empty())
//     return false;
//   const auto *Parent = Parents[0].get<Stmt>();
//   if (!Parent)
//     return false;
//   for (const Stmt *Child : Parent->children()) {
//     return *dyn_cast<Expr>(Child) == Node;
//   }
// }

} // namespace clang
} // namespace ast_matchers

namespace clang {
namespace tidy {
namespace misc {

using namespace ::clang::ast_matchers;
using namespace ::clang::transformer;

RewriteRuleWith<std::string> FunctionCallTracingCheckImpl() {
  std::cerr << "[*] FunctionCallTracingCheckImpl" << std::endl;

  auto add_include = addInclude("trace.h", IncludeFormat::Angled);
  // auto add_include = addInclude("trace.h");

  auto function_found = [](auto rule_name) { return cat("Function declaration found 🎈 (", rule_name, ")"); };
  auto return_found = [](auto rule_name) { return cat("Return statement found 📢 (", rule_name, ")"); };

/*
|-LinkageSpecDecl 0x1649e50 <line:79:1, line:401:1> line:79:8 C
[...]
| |-CXXRecordDecl 0x164ba40 prev 0x1649cd0 <line:95:1, line:99:1> line:95:8 referenced struct tiffis_data definition
| | |-DefinitionData pass_in_registers aggregate standard_layout trivially_copyable
[...]
| | |-CXXRecordDecl 0x164bb38 <col:1, col:8> col:8 implicit struct tiffis_data
| | |-FieldDecl 0x164bc08 <line:97:2, col:11> col:11 referenced stream 'std::istream *'
| | |-FieldDecl 0x164e1c8 <line:98:9, col:23> col:23 referenced start_pos 'ios::pos_type':'std::fpos<__mbstate_t>'
| | |-CXXConstructorDecl 0x164e260 <line:95:8> col:8 implicit constexpr tiffis_data 'void (const tiffis_data &)' inline default trivial noexcept-unevaluated 0x164e260
| | | `-ParmVarDecl 0x164e378 <col:8> col:8 'const tiffis_data &'
[...]
*/
  // TODO: コンストラクタのトレース
  auto HandleCXXConstructorDecl = makeRule(
    cxxConstructorDecl(),
    add_include, // Do nothing
    function_found("HandleCXXConstructorDecl")
  );

  auto HandleDefaultedCXXDestructorDecl = makeRule(
    cxxDestructorDecl(isDefaulted()),
    add_include, // Do nothing
    function_found("HandleDefaultedCXXDestructorDecl")
  );

/*
|-FunctionDecl 0x20dc9e0 <line:7:1, line:9:1> line:7:5 used add 'int (int, int)'
| |-ParmVarDecl 0x20dc880 <col:9, col:13> col:13 used x 'int'
| |-ParmVarDecl 0x20dc900 <col:16, col:20> col:20 used y 'int'
| `-CompoundStmt 0x20dcb30 <col:23, line:9:1>
|   `-ReturnStmt 0x20dcb20 <line:8:5, col:16>
*/
  auto capture_body = hasBody(compoundStmt().bind("body"));
  auto capture_paramvardecl = [](unsigned N) { 
      return hasParameter(
        N,
        parmVarDecl(
          hasTypeLoc(typeLoc().bind("param_type" + std::to_string(N)))
        ).bind("param" + std::to_string(N))
      );
    };
  auto change_paramvardecl = [](unsigned N) { 
      return insertBefore(
        node("body"),
        cat(
          "__trace_function_param_decl(",
          name("param" + std::to_string(N)),
          ", (",
          name("param_type" + std::to_string(N)),
          ")); "
        )
      );
    };
  auto change_paramvardecl_begin = insertBefore(node("body"), cat("{ __trace_function_call_enter(); "));
  auto change_paramvardecl_terminal = insertAfter(node("body"), cat(" __trace_void_function_return(); }"));
  auto HandleFunctionDecl0 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        unless(hasParent(cxxRecordDecl())),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl0")
    );
  auto HandleFunctionDecl1 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl1")
    );
  auto HandleFunctionDecl2 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl2")
    );
  auto HandleFunctionDecl3 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl3")
    );
  auto HandleFunctionDecl4 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl4")
    );
  auto HandleFunctionDecl5 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl5")
    );
  auto HandleFunctionDecl6 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl6")
    );
  auto HandleFunctionDecl7 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl(6),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl7")
    );
  auto HandleFunctionDecl8 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl8")
    );
  auto HandleFunctionDecl9 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl9")
    );
  auto HandleFunctionDecl10 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
        capture_paramvardecl(9),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl(9),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl10")
    );
  auto HandleFunctionDecl11 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
        capture_paramvardecl(9),
        capture_paramvardecl(10),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl(9),
        change_paramvardecl(10),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl11")
    );
  auto HandleFunctionDecl12 = makeRule(
      functionDecl(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        capture_paramvardecl(0),
        capture_paramvardecl(1),
        capture_paramvardecl(2),
        capture_paramvardecl(3),
        capture_paramvardecl(4),
        capture_paramvardecl(5),
        capture_paramvardecl(6),
        capture_paramvardecl(7),
        capture_paramvardecl(8),
        capture_paramvardecl(9),
        capture_paramvardecl(10),
        capture_paramvardecl(11),
        capture_body
      ),
      {
        change_paramvardecl_begin,
        change_paramvardecl(0),
        change_paramvardecl(1),
        change_paramvardecl(2),
        change_paramvardecl(3),
        change_paramvardecl(4),
        change_paramvardecl(5),
        change_paramvardecl(6),
        change_paramvardecl(7),
        change_paramvardecl(8),
        change_paramvardecl(9),
        change_paramvardecl(10),
        change_paramvardecl(11),
        change_paramvardecl_terminal,
        add_include,
      },
      function_found("HandleFunctionDecl12")
    );

  // 関数呼び出しの呼び出し元と呼び出し先の値のマッチング
  // <CallExpr>
/*
|       `-CallExpr 0x152d610 <col:13, col:21> 'int'
|         |-ImplicitCastExpr 0x152d5f8 <col:13> 'int (*)(int, int)' <FunctionToPointerDecay>
|         | `-DeclRefExpr 0x152d568 <col:13> 'int (int, int)' Function 0x152b9c0 'add' 'int (int, int)'
|         |-IntegerLiteral 0x152d588 <col:17> 'int' 1
|         `-ImplicitCastExpr 0x152d640 <col:20> 'int' <LValueToRValue>
|           `-DeclRefExpr 0x152d5a8 <col:20> 'int' lvalue Var 0x152d430 'y' 'int'
*/
/*
|   |-DeclStmt 0x23cac08 <line:74:5, col:34>
|   | `-VarDecl 0x23cab68 <col:5, col:28> col:12 used var_void_f 'void (*)()' cinit
|   |   `-ImplicitCastExpr 0x23cabf0 <col:28> 'void (*)()' <FunctionToPointerDecay>
|   |     `-DeclRefExpr 0x23cabd0 <col:28> 'void ()' Function 0x23c4ed8 'void_f' 'void ()'
|   |-CallExpr 0x23cac58 <line:75:5, col:16> 'void'
|   | `-ImplicitCastExpr 0x23cac40 <col:5> 'void (*)()' <LValueToRValue>
|   |   `-DeclRefExpr 0x23cac20 <col:5> 'void (*)()' lvalue Var 0x23cab68 'var_void_f' 'void (*)()'
*/
  auto ignores_for_callExpr = allOf(
    unless(isInMacro()),
    unless(isExpansionInSystemHeader()),
    isExpansionInMainFile(),
    unless(returnsVoid()),
    unless(callee(functionDecl(isBuiltinFunction()))),
    unless(cxxOperatorCallExpr()),
    unless(hasAncestor(forStmt())), // ゆるすぎるかも…
    unless(hasAncestor(cxxForRangeStmt()))
  );
  auto HandleCallExpr = makeRule(
      callExpr(
        ignores_for_callExpr,
        callee(expr().bind("callee"))
      ).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_function_call(")),
        insertAfter(node("caller"), cat(", ", node("callee"), ")")),
        add_include,
      },
      cat("HandleCallExpr")
    );
/*
| |     `-CallExpr 0x2916b10 <col:31, col:42> 'typename std::remove_reference<unique_ptr<int> &>::type':'std::unique_ptr<int>' xvalue
| |       |-ImplicitCastExpr 0x2916af8 <col:31, col:36> 'typename std::remove_reference<unique_ptr<int> &>::type &&(*)(std::unique_ptr<int> &) noexcept' <FunctionToPointerDecay>
| |       | `-DeclRefExpr 0x29168c8 <col:31, col:36> 'typename std::remove_reference<unique_ptr<int> &>::type &&(std::unique_ptr<int> &) noexcept' lvalue Function 0x29167c8 'move' 'typename std::remove_reference<unique_ptr<int> &>::type &&(std::unique_ptr<int> &) noexcept' (FunctionTemplate 0x1d59088 'move')
| |       `-DeclRefExpr 0x2916100 <col:41> 'std::unique_ptr<int>':'std::unique_ptr<int>' lvalue ParmVar 0x28e61a0 'x' 'std::unique_ptr<int>':'std::unique_ptr<int>'
*/
  auto HandleExplicitMoveCallExpr = makeRule(
      callExpr(callee(
        functionDecl(hasName("move")).bind("callee")
      )).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_function_call_with_cleanups(")),
        insertAfter(node("caller"), cat(", ", node("callee"), ")")),
        add_include,
      },
      cat("HandleExplicitMoveCallExpr")
    );

/* `auto a = std::make_unique<Object>(objNull);`
|   |-DeclStmt 0x24ebf48 <line:70:5, col:47>
|   | `-VarDecl 0x24587e8 <col:5, col:46> col:10 used a 'typename _MakeUniq<Object>::__single_object':'std::unique_ptr<Object>' cinit destroyed
|   |   `-ExprWithCleanups 0x24ebf30 <col:14, col:46> 'typename _MakeUniq<Object>::__single_object':'std::unique_ptr<Object>'
|   |     `-CXXConstructExpr 0x24ebf00 <col:14, col:46> 'typename _MakeUniq<Object>::__single_object':'std::unique_ptr<Object>' 'void (std::unique_ptr<Object> &&) noexcept' elidable
|   |       `-MaterializeTemporaryExpr 0x24eb938 <col:14, col:46> 'typename _MakeUniq<Object>::__single_object':'std::unique_ptr<Object>' xvalue
|   |         `-CXXBindTemporaryExpr 0x24e4cd0 <col:14, col:46> 'typename _MakeUniq<Object>::__single_object':'std::unique_ptr<Object>' (CXXTemporary 0x24e4cd0)
|   |           `-CallExpr 0x2459940 <col:14, col:46> 'typename _MakeUniq<Object>::__single_object':'std::unique_ptr<Object>'
|   |             |-ImplicitCastExpr 0x2459928 <col:14, col:37> 'typename _MakeUniq<Object>::__single_object (*)(ObjType &&)' <FunctionToPointerDecay>
|   |             | `-DeclRefExpr 0x2459868 <col:14, col:37> 'typename _MakeUniq<Object>::__single_object (ObjType &&)' lvalue Function 0x24594a8 'make_unique' 'typename _MakeUniq<Object>::__single_object (ObjType &&)' (FunctionTemplate 0x21acc38 'make_unique')
|   |             `-MaterializeTemporaryExpr 0x24e4cb0 <col:39> 'ObjType':'ObjType' xvalue
|   |               `-DeclRefExpr 0x2458928 <col:39> 'ObjType' EnumConstant 0x24577c0 'objNull' 'ObjType'
*/
/* `obj1 = dict->lookup("S");`
|   |-ExprWithCleanups 0x3d5a4f8 <line:615:5, col:28> 'Object' lvalue
|   | `-CXXOperatorCallExpr 0x3d5a4c0 <col:5, col:28> 'Object' lvalue '='
|   |   |-ImplicitCastExpr 0x3d5a4a8 <col:10> 'Object &(*)(Object &&) noexcept' <FunctionToPointerDecay>
|   |   | `-DeclRefExpr 0x3d5a488 <col:10> 'Object &(Object &&) noexcept' lvalue CXXMethod 0x1d83770 'operator=' 'Object &(Object &&) noexcept'
|   |   |-DeclRefExpr 0x3d5a2c0 <col:5> 'Object' lvalue Var 0x3d59ea0 'obj1' 'Object'
|   |   `-MaterializeTemporaryExpr 0x3d5a470 <col:12, col:28> 'Object' xvalue
|   |     `-CXXBindTemporaryExpr 0x3d5a450 <col:12, col:28> 'Object' (CXXTemporary 0x3d5a450)
|   |       `-CXXMemberCallExpr 0x3d5a3c8 <col:12, col:28> 'Object'
|   |         |-MemberExpr 0x3d5a398 <col:12, col:18> '<bound member function type>' ->lookup 0x22eb730
|   |         | `-ImplicitCastExpr 0x3d5a3f8 <col:12> 'const Dict *' <NoOp>
|   |         |   `-ImplicitCastExpr 0x3d5a300 <col:12> 'Dict *' <LValueToRValue>
|   |         |     `-DeclRefExpr 0x3d5a2e0 <col:12> 'Dict *' lvalue ParmVar 0x3d59cb0 'dict' 'Dict *'
|   |         |-ImplicitCastExpr 0x3d5a410 <col:25> 'const char *' <ArrayToPointerDecay>
|   |         | `-StringLiteral 0x3d5a378 <col:25> 'const char[2]' lvalue "S"
|   |         `-CXXDefaultArgExpr 0x3d5a428 <<invalid sloc>> 'int'
*/
/* 除外したいケース `array.push(std::move(a));`
| `-CompoundStmt 0x13c3388 <col:18, line:63:1>
[...]
|   |-ExprWithCleanups 0x13c22c0 <line:61:5, col:28> 'void'
|   | `-CXXMemberCallExpr 0x13c1430 <col:5, col:28> 'void'
|   |   |-MemberExpr 0x13c1258 <col:5, col:11> '<bound member function type>' .push 0x138d658
|   |   | `-DeclRefExpr 0x13c1238 <col:5> 'Array' lvalue Var 0x13bf1a0 'array' 'Array'
|   |   `-CXXBindTemporaryExpr 0x13c22a0 <col:16, col:27> 'std::unique_ptr<int>':'std::unique_ptr<int>' (CXXTemporary 0x13c22a0)
|   |     `-CXXConstructExpr 0x13c2268 <col:16, col:27> 'std::unique_ptr<int>':'std::unique_ptr<int>' 'void (std::unique_ptr<int> &&) noexcept'
|   |       `-CallExpr 0x13c1408 <col:16, col:27> 'typename std::remove_reference<unique_ptr<int> &>::type':'std::unique_ptr<int>' xvalue
|   |         |-ImplicitCastExpr 0x13c13f0 <col:16, col:21> 'typename std::remove_reference<unique_ptr<int> &>::type &&(*)(std::unique_ptr<int> &) noexcept' <FunctionToPointerDecay>
|   |         | `-DeclRefExpr 0x13c13b8 <col:16, col:21> 'typename std::remove_reference<unique_ptr<int> &>::type &&(std::unique_ptr<int> &) noexcept' lvalue Function 0x13bdc78 'move' 'typename std::remove_reference<unique_ptr<int> &>::type &&(std::unique_ptr<int> &) noexcept' (FunctionTemplate 0x800088 'move')
|   |         `-DeclRefExpr 0x13c12f8 <col:26> 'typename _MakeUniq<int>::__single_object':'std::unique_ptr<int>' lvalue Var 0x13bf368 'a' 'typename _MakeUniq<int>::__single_object':'std::unique_ptr<int>'
*/
  auto HandleImplicitCleanupsCallExpr = makeRule(
      callExpr(
        // unless(returnsVoid()), // NOTE: 戻り値が void な関数呼び出しを除外
        hasAncestor(exprWithCleanups()),
        callee(expr().bind("callee"))
      ).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_function_call_with_cleanups(")),
        insertAfter(node("caller"), cat(", ", node("callee"), ")")),
        add_include,
      },
      cat("HandleImplicitCleanupsCallExpr")
    );

  auto HandleVoidCallExpr = makeRule(
      callExpr(
        unless(isInMacro()),
        unless(isExpansionInSystemHeader()),
        isExpansionInMainFile(),
        unless(callee(functionDecl(isBuiltinFunction()))),
        returnsVoid(),
        callee(expr().bind("callee"))
      ).bind("caller"),
      {
        insertBefore(node("caller"), cat("__trace_void_function_call(")),
        insertAfter(node("caller"), cat(", ", node("callee"), ")")),
        add_include,
      },
      cat("HandleVoidCallExpr")
    );


/*
|-FunctionDecl 0x2268fb8 </usr/lib/llvm-14/lib/clang/14.0.5/include/stdbool.h:15:14, bad.c:51:1> line:24:6 used test_int 'bool ()'
| `-CompoundStmt 0x226a130 <col:17, line:51:1>
[...]
|   |-CallExpr 0x2269810 <line:37:5, col:8> 'int'
|   | |-ImplicitCastExpr 0x22697f8 <col:5> 'int (*)(int)' <FunctionToPointerDecay>
|   | | `-DeclRefExpr 0x2269788 <col:5> 'int (int)' Function 0x2266ea8 'f' 'int (int)'
|   | `-IntegerLiteral 0x22697a8 <col:7> 'int' 1
*/
  auto callexpr_with_return_value = callExpr(
      unless(callee(functionDecl(isBuiltinFunction()))),
      unless(returnsVoid())
    ).bind("caller");
  auto HandleUnuseReturnValueCallExpr = makeRule(
      stmt(anyOf(
        ifStmt(hasThen(callexpr_with_return_value)),
        ifStmt(hasElse(callexpr_with_return_value)),
        labelStmt(callexpr_with_return_value),
        compoundStmt(callexpr_with_return_value)
      )),
      {
        insertBefore(node("caller"), cat("__trace_unused_function_return_value(")),
        insertAfter(node("caller"), cat(")")),
        add_include,
      },
      cat("HandleUnuseReturnValueCallExpr")
    );
  
  auto HandleCXXOperatorCallExpr = makeRule(
    cxxOperatorCallExpr(),
    {},
    cat("HandleCXXOperatorCallExpr")
  );

/*
|       `-CXXMemberCallExpr 0xfcd050 <col:13, col:26> 'int'
|         |-MemberExpr 0xfccfe0 <col:13, col:18> '<bound member function type>' .add 0xfcbe70
|         | `-DeclRefExpr 0xfccfc0 <col:13> 'Calculator' lvalue Var 0xfcc0e8 'calc' 'Calculator'
|         |-IntegerLiteral 0xfcd010 <col:22> 'int' 1
|         `-IntegerLiteral 0xfcd030 <col:25> 'int' 2
*/
  auto is_function_pointer = implicitCastExpr(hasCastKind(CK_FunctionToPointerDecay));
  auto ignores_for_CallExprArgument = allOf(
      unless(hasAncestor(forStmt())), // ゆるすぎるかも…
      unless(hasAncestor(cxxForRangeStmt())),
      unless(hasParent(cxxMemberCallExpr())),
      unless(hasParent(cxxOperatorCallExpr()))
  );
  auto HandleCallExprArgument = makeRule(
      stmt(
        // NOTE: HandleCalleeFunctionDeclRefExpr との重複適用に注意
        unless(is_function_pointer),
        ignores_for_CallExprArgument,
        hasParent(callExpr(
          unless(callee(functionDecl(isBuiltinFunction()))),
          unless(isInMacro())
        ))
      ).bind("argument"),
      {
        insertBefore(node("argument"), cat("__trace_function_call_param(")),
        insertAfter(node("argument"), cat(")")),
        add_include,
      },
      cat("HandleCallExprArgument")
    );

/* 📝 g(NULL, 3) の AST
|   |     `-CallExpr 0x15ee820 <col:20, col:29> 'int'
|   |       |-ImplicitCastExpr 0x15ee808 <col:20> 'int (*)(void *, int)' <FunctionToPointerDecay>
|   |       | `-DeclRefExpr 0x15ee708 <col:20> 'int (void *, int)' Function 0x15e8150 'g' 'int (void *, int)'
|   |       |-ParenExpr 0x15ee788 </usr/lib/llvm-14/lib/clang/14.0.5/include/stddef.h:89:16, col:25> 'void *'
|   |       | `-CStyleCastExpr 0x15ee760 <col:17, col:24> 'void *' <NullToPointer>
|   |       |   `-IntegerLiteral 0x15ee728 <col:24> 'int' 0
|   |       `-IntegerLiteral 0x15ee7a8 <bad.c:107:28> 'int' 3
*/
  auto HandleCallNullArgument = makeRule(
      expr(parenExpr(
        cStyleCastExpr(
          hasCastKind(CK_NullToPointer)
        )
      )).bind("argument"),
      {
        insertBefore(node("argument"), cat("__trace_function_call_param(")),
        insertAfter(node("argument"), cat(")")),
        add_include,
      },
      cat("HandleCallNullArgument")
    );

/*
|   |-DeclStmt 0x14f1470 <line:62:5, col:34>
|   | `-VarDecl 0x14f1228 <col:5, col:33> col:9 w 'int' cinit
|   |   `-CallExpr 0x14f1448 <col:13, col:33> 'int'
|   |     |-ImplicitCastExpr 0x14f1430 <col:13> 'int (*)(int)' <FunctionToPointerDecay>
|   |     | `-DeclRefExpr 0x14f1290 <col:13> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |     `-BinaryOperator 0x14f1410 <col:15, col:32> 'int' '+'
|   |       |-CallExpr 0x14f1308 <col:15, col:20> 'int'
|   |       | |-ImplicitCastExpr 0x14f12f0 <col:15> 'int (*)(int)' <FunctionToPointerDecay>
|   |       | | `-DeclRefExpr 0x14f12b0 <col:15> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |       | `-IntegerLiteral 0x14f12d0 <col:17> 'int' 101
|   |       `-CallExpr 0x14f13e8 <col:24, col:32> 'int'
|   |         |-ImplicitCastExpr 0x14f13d0 <col:24> 'int (*)(int)' <FunctionToPointerDecay>
|   |         | `-DeclRefExpr 0x14f1330 <col:24> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |         `-CallExpr 0x14f13a8 <col:26, col:31> 'int'
|   |           |-ImplicitCastExpr 0x14f1390 <col:26> 'int (*)(int)' <FunctionToPointerDecay>
|   |           | `-DeclRefExpr 0x14f1350 <col:26> 'int (int)' Function 0x14eab58 'f' 'int (int)'
|   |           `-IntegerLiteral 0x14f1370 <col:28> 'int' 102
*/
  auto HandleFunctionCallCallExprArgument = makeRule(
      callExpr(
        ignores_for_CallExprArgument,
        hasParent(callExpr()),
        callee(expr().bind("callee"))
      ).bind("argument"),
      {
        insertBefore(node("argument"), cat("__trace_function_call_param(__trace_function_call(")),
        insertAfter(node("argument"), cat(",", node("callee"), "))")),
        add_include,
      },
      cat("HandleFunctionCallCallExprArgument")
    );

/* `return std::move(this->array.back());`
| |   `-ReturnStmt 0x15aa068 <line:50:9, col:44>
| |     `-CXXConstructExpr 0x15aa038 <col:16, col:44> 'std::unique_ptr<int>':'std::unique_ptr<int>' 'void (std::unique_ptr<int> &&) noexcept'
| |       `-CallExpr 0x15a9200 <col:16, col:44> 'typename std::remove_reference<unique_ptr<int> &>::type':'std::unique_ptr<int>' xvalue
| |         |-ImplicitCastExpr 0x15a91e8 <col:16, col:21> 'typename std::remove_reference<unique_ptr<int> &>::type &&(*)(std::unique_ptr<int> &) noexcept' <FunctionToPointerDecay>
| |         | `-DeclRefExpr 0x15a91b0 <col:16, col:21> 'typename std::remove_reference<unique_ptr<int> &>::type &&(std::unique_ptr<int> &) noexcept' lvalue Function 0x15a8c38 'move' 'typename std::remove_reference<unique_ptr<int> &>::type &&(std::unique_ptr<int> &) noexcept' (FunctionTemplate 0x9eb088 'move')
| |         `-CXXMemberCallExpr 0x15a9158 <col:26, col:43> '__gnu_cxx::__alloc_traits<std::allocator<std::unique_ptr<int>>, std::unique_ptr<int>>::value_type':'std::unique_ptr<int>' lvalue
| |           `-MemberExpr 0x15a9128 <col:26, col:38> '<bound member function type>' .back 0x1599ec8
| |             `-MemberExpr 0x15a9098 <col:26, col:32> 'std::vector<std::unique_ptr<int>>':'std::vector<std::unique_ptr<int>>' lvalue ->array 0x15a6260
| |               `-CXXThisExpr 0x15a9088 <col:26> 'Array *' this
*/
  auto HandleCXXConstructExprFunctionCallCallExprArgument = makeRule(
      callExpr(
        ignores_for_CallExprArgument,
        hasParent(callExpr()),
        hasAncestor(cxxConstructExpr()),
        callee(expr().bind("callee"))
      ).bind("argument"),
      {
        insertBefore(node("argument"), cat("__trace_function_call_param(__trace_function_call_with_cleanups2(")),
        insertAfter(node("argument"), cat(",", node("callee"), "))")),
        add_include,
      },
      cat("HandleCXXConstructExprFunctionCallCallExprArgument")
    );

/* `reference_count = 1`
| |   `-CXXOperatorCallExpr 0x2052a60 <line:27:9, col:27> 'std::__atomic_base<int>::__int_type':'int' '='
| |     |-ImplicitCastExpr 0x2052a48 <col:25> 'std::__atomic_base<int>::__int_type (*)(std::__atomic_base<int>::__int_type) noexcept' <FunctionToPointerDecay>
| |     | `-DeclRefExpr 0x20529c8 <col:25> 'std::__atomic_base<int>::__int_type (std::__atomic_base<int>::__int_type) noexcept' lvalue CXXMethod 0x1fd7070 'operator=' 'std::__atomic_base<int>::__int_type (std::__atomic_base<int>::__int_type) noexcept'
| |     |-ImplicitCastExpr 0x20529a8 <col:9> 'std::__atomic_base<int>' lvalue <UncheckedDerivedToBase (__atomic_base)>
| |     | `-MemberExpr 0x2052440 <col:9> 'std::atomic_int':'std::atomic<int>' lvalue ->reference_count 0x2051ac0
| |     |   `-CXXThisExpr 0x2052430 <col:9> 'Array *' implicit this
| |     `-IntegerLiteral 0x2052470 <col:27> 'int' 1
*/
  auto HandleCalleeFunctionDeclRefExpr = makeRule(
      // NOTE: なぜか implicitCastExpr() とマッチさせようとするとルールが発火しない
      declRefExpr(
        unless(hasParent(
          implicitCastExpr(
            hasCastKind(CK_FunctionToPointerDecay),
            hasParent(cxxOperatorCallExpr())
          )
        )),
        hasAncestor(implicitCastExpr(
          hasCastKind(CK_FunctionToPointerDecay),
          hasParent(callExpr(
            unless(isInMacro())
          ))
        ))
      ).bind("callee"),
      {
        insertBefore(node("callee"), cat("__trace_function_call_param(")),
        insertAfter(node("callee"), cat(")")),
        add_include,
      },
      cat("HandleCalleeFunctionDeclRefExpr")
    );
  // auto HandleCalleeFunctionDeclRefExpr2 = makeRule(
  //     // NOTE: なぜか implicitCastExpr() とマッチさせようとするとルールが発火しない
  //     stmt(implicitCastExpr(
  //       hasParent(callExpr()),
  //       hasCastKind(CK_FunctionToPointerDecay),
  //       declRefExpr()
  //     )).bind("callee"),
  //     {
  //       insertBefore(node("callee"), cat("__trace_function_call_param(")),
  //       insertAfter(node("callee"), cat(")")),
  //       add_include,
  //     },
  //     cat("HandleCalleeFunctionDeclRefExpr2")
  //   );

  auto HandleReturnStmt = makeRule(
      returnStmt(
        unless(hasAncestor(cxxRecordDecl())),
        // hasAncestor(functionDecl(hasReturnTypeLoc(typeLoc().bind("ReturnValueType")))),
        hasReturnValue(expr().bind("ReturnValue"))
      ),
      {
        // NOTE: return(ret_val); と書いている例もあるので、安全のためにカッコで囲んでおく
        insertBefore(node("ReturnValue"), cat("(__trace_function_return(")),
        insertAfter(node("ReturnValue"), cat("))")),
        // insertAfter(node("ReturnValue"), cat(", ", name("ReturnValueType"), "))")),
        add_include,
      },
      return_found("HandleReturnStmt")
    );

/*
|   `-ReturnStmt 0xbd4068 <line:456:5, col:17>
|     `-ImplicitCastExpr 0xbd4050 <col:12, col:17> 'int' <IntegralCast>
|       `-ImplicitCastExpr 0xbd4038 <col:12, col:17> 'unsigned int' <LValueToRValue>
|         `-MemberExpr 0xbd4008 <col:12, col:17> 'unsigned int' lvalue bitfield ->ischild 0xbd3b68
|           `-ImplicitCastExpr 0xbd3ff0 <col:12> 'struct ossl_lib_ctx_st *' <LValueToRValue>
|             `-DeclRefExpr 0xbd3fd0 <col:12> 'struct ossl_lib_ctx_st *' lvalue ParmVar 0xbd3c70 'ctx' 'struct ossl_lib_ctx_st *'
*/
  auto HandleBitFieldReturnStmt = makeRule(
      returnStmt(
        has(ignoringParenImpCasts(memberExpr(hasDeclaration(fieldDecl(isBitField()))))),
        hasReturnValue(expr().bind("ReturnValue"))
      ),
      {
        // NOTE: +(x) で bit-filed をデフォルトの型に変換できる (ref. https://stackoverflow.com/a/62867037)
        insertBefore(node("ReturnValue"), cat("(__trace_function_return(+(")),
        insertAfter(node("ReturnValue"), cat(")))")),
        add_include,
      },
      return_found("HandleBitFieldReturnStmt")
    );

/* `return std::nullptr;`
|   `-ReturnStmt 0x1fe6218 <line:26:5, col:12>
|     `-ExprWithCleanups 0x1fe6200 <col:5, col:12> 'std::unique_ptr<int>':'std::unique_ptr<int>'
|       `-CXXConstructExpr 0x1fe61d0 <col:5, col:12> 'std::unique_ptr<int>':'std::unique_ptr<int>' 'void (std::unique_ptr<int> &&) noexcept' elidable
|         `-MaterializeTemporaryExpr 0x1fe61b8 <col:12> 'std::unique_ptr<int>':'std::unique_ptr<int>' xvalue
|           `-CXXBindTemporaryExpr 0x1fd85a0 <col:12> 'std::unique_ptr<int>':'std::unique_ptr<int>' (CXXTemporary 0x1fd85a0)
|             `-ImplicitCastExpr 0x1fd8580 <col:12> 'std::unique_ptr<int>':'std::unique_ptr<int>' <ConstructorConversion>
|               `-CXXConstructExpr 0x1fd8550 <col:12> 'std::unique_ptr<int>':'std::unique_ptr<int>' 'void (std::nullptr_t) noexcept'
|                 `-CXXNullPtrLiteralExpr 0x1fd6950 <col:12> 'std::nullptr_t'
*/
  auto HandleCXXConstructExprReturnStmt = makeRule(
      returnStmt(
        hasDescendant(cxxConstructExpr(
          has(expr().bind("ReturnValue"))
        ))
      ),
      {
        insertBefore(node("ReturnValue"), cat("(__trace_function_return_with_cleanups(")),
        insertAfter(node("ReturnValue"), cat("))")),
        add_include,
      },
      return_found("HandleCXXConstructExprReturnStmt")
    );

  return applyFirst({
    HandleCXXConstructorDecl,
    HandleDefaultedCXXDestructorDecl,

    HandleFunctionDecl12,
    HandleFunctionDecl11,
    HandleFunctionDecl10,
    HandleFunctionDecl9,
    HandleFunctionDecl8,
    HandleFunctionDecl7,
    HandleFunctionDecl6,
    HandleFunctionDecl5,
    HandleFunctionDecl4,
    HandleFunctionDecl3,
    HandleFunctionDecl2,
    HandleFunctionDecl1,
    HandleFunctionDecl0,

    HandleBitFieldReturnStmt,
    HandleCXXConstructExprReturnStmt,
    HandleReturnStmt,

    // Match with CallExpr
    HandleCXXConstructExprFunctionCallCallExprArgument,
    HandleFunctionCallCallExprArgument,
    HandleCXXOperatorCallExpr,
    HandleExplicitMoveCallExpr,
    HandleImplicitCleanupsCallExpr,
    HandleCalleeFunctionDeclRefExpr,
    HandleCallExpr,
    HandleVoidCallExpr,
    HandleUnuseReturnValueCallExpr,

    // Match with stmt
    HandleCallNullArgument,
    HandleCallExprArgument, // __trace_variable_rvalue と両立しない（例：f(x, 1)）のでChekerを分けている

    // HandleMacroUse,
  });
}

FunctionCallTracingCheck::FunctionCallTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(FunctionCallTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
