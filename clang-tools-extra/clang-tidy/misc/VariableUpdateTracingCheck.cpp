//===--- VariableUpdateTracingCheck.cpp - clang-tidy ----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "VariableUpdateTracingCheck.h"
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

namespace clang {
namespace ast_matchers {

AST_MATCHER(VarDecl, isRegister) {
  return Node.getStorageClass() == SC_Register;
}

AST_MATCHER(VarDecl, hasConstantInitialization) {
  return Node.hasConstantInitialization();
}

// NOTE: rvalue な expr も暗黙に含む
AST_MATCHER(Expr, isLValue) {
  return Node.isLValue();
}

AST_MATCHER(ImplicitCastExpr, isLValueToRValue) {
  return Node.getCastKind() == CK_LValueToRValue;
}

AST_MATCHER(Expr, isInMacro) {
  return Node.getBeginLoc().isMacroID();
}

AST_MATCHER(FieldDecl, hasIntBitwidth) {
  assert(Node.isBitField());
  const ASTContext &Ctx = Node.getASTContext();
  unsigned IntBitWidth = Ctx.getIntWidth(Ctx.IntTy);
  unsigned CurrentBitWidth = Node.getBitWidthValue(Ctx);
  return IntBitWidth == CurrentBitWidth;
}

AST_MATCHER(QualType, isShortInt) {
  auto ctype = Node.getCanonicalType();
  if (ctype->isBuiltinType()) {
    auto kind = dyn_cast<BuiltinType>(ctype.getTypePtr())->getKind();
    return kind == BuiltinType::Short || kind == BuiltinType::UShort || kind == BuiltinType::SChar || kind == BuiltinType::UChar;
  } else {
    return false;
  }
}

AST_MATCHER(VarDecl, hasAlignedAttr) {
  return Node.hasAttr<AlignedAttr>();
}



} // namespace clang
} // namespace ast_matchers

namespace clang {
namespace tidy {
namespace misc {

using namespace ::clang::ast_matchers;
using namespace ::clang::transformer;

RewriteRuleWith<std::string> VariableUpdateTracingCheckImpl() {
  std::cerr << "[*] VariableUpdateTracingCheckImpl" << std::endl;

  auto declaration_found = [](auto rule_name) { return cat("Variable declaration found 📢 (", rule_name, ")"); };
  auto assignment_found = [](auto rule_name) { return cat("Assignment found 🎉 (", rule_name, ")"); };

/*
|   `-ReturnStmt 0x24378d8 <line:194:5, col:12>
|     `-CXXConstructExpr 0x24378a8 <col:12> 'std::unique_ptr<Rectangle>':'std::unique_ptr<Rectangle>' 'void (std::unique_ptr<Rectangle> &&) noexcept'
|       `-ImplicitCastExpr 0x2437860 <col:12> 'typename _MakeUniq<Rectangle>::__single_object':'std::unique_ptr<Rectangle>' xvalue <NoOp>
|         `-DeclRefExpr 0x2436a68 <col:12> 'typename _MakeUniq<Rectangle>::__single_object':'std::unique_ptr<Rectangle>' lvalue Var 0x242d050 'rect' 'typename _MakeUniq<Rectangle>::__single_object':'std::unique_ptr<Rectangle>'
*/
  auto is_rvalue = hasAncestor(implicitCastExpr(
      unless(hasParent(cStyleCastExpr(hasCastKind(CK_ToVoid)))),
      anyOf(
        hasCastKind(CK_ArrayToPointerDecay),
        // hasCastKind(CK_NoOp), // => error: call to deleted constructor of 'std::unique_ptr<Rectangle>'
        hasCastKind(CK_LValueToRValue)
      )
    ));
  auto is_lvalue = allOf(
      // unless(is_rvalue),
      hasParent(binaryOperator(hasOperatorName("="))),
      unless(hasParent(whileStmt())),
      isLValue()
    );
  auto is_referenced_value = hasAncestor(unaryOperator(hasOperatorName("&")));
  auto is_array_subscription = hasAncestor(arraySubscriptExpr());

  // __trace_??? 関数呼び出し内ではマッチさせない
  // => マクロなので関数として認識されない！
  // auto HandleTraceFunctionCall = makeRule(
  //   callExpr(callee(functionDecl(hasAnyName(
  //     "__trace_variable_declaration", 
  //     "__trace_variable_lvalue",
  //     "__trace_variable_rvalue"
  //   )))).bind("expr"),
  //   changeTo(node("expr"), cat(node("expr"))),
  //   cat("Trace function found 🤫")
  // );

/* (1)
|   |-DeclStmt 0x152bad8 <line:40:5, col:16>
|   | `-VarDecl 0x152ba08 <col:5, col:15> col:9 w 'int' cinit
|   |   `-ImplicitCastExpr 0x152bac0 <col:13, col:15> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x152ba90 <col:13, col:15> 'int' lvalue .b 0x152af30
|   |       `-DeclRefExpr 0x152ba70 <col:13> 'struct pair':'struct pair' lvalue Var 0x152b570 'p' 'struct pair':'struct pair'
*/
/* (2)
|   |-DeclStmt 0x1e5a358 <line:60:5, col:34>
|   | `-VarDecl 0x1e5a240 <col:5, col:28> col:9 length 'int' cinit
|   |   `-ImplicitCastExpr 0x1e5a340 <col:18, col:28> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x1e5a310 <col:18, col:28> 'int' lvalue .length 0x1e59a78
|   |       `-MemberExpr 0x1e5a2e0 <col:18, col:21> 'struct (unnamed struct at bad.c:51:5)':'struct header::(unnamed at bad.c:51:5)' lvalue ->nested 0x1e59b28
|   |         `-ImplicitCastExpr 0x1e5a2c8 <col:18> 'struct header *' <LValueToRValue>
|   |           `-DeclRefExpr 0x1e5a2a8 <col:18> 'struct header *' lvalue Var 0x1e5a090 'h' 'struct header *'
*/
/* (3)
|   |-DeclStmt 0x186ad90 <line:65:5, col:39>
|   | `-VarDecl 0x186ac48 <col:5, col:34> col:9 value 'int' cinit
|   |   `-ImplicitCastExpr 0x186ad78 <col:17, col:34> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x186ad48 <col:17, col:34> 'int' lvalue .value 0x1869d88
|   |       `-MemberExpr 0x186ad18 <col:17, col:27> 'struct (unnamed struct at bad.c:54:9)':'struct header::(unnamed at bad.c:54:9)' lvalue .nested 0x1869e38
|   |         `-MemberExpr 0x186ace8 <col:17, col:20> 'struct (unnamed struct at bad.c:52:5)':'struct header::(unnamed at bad.c:52:5)' lvalue ->nested 0x1869ee8
|   |           `-ImplicitCastExpr 0x186acd0 <col:17> 'struct header *' <LValueToRValue>
|   |             `-DeclRefExpr 0x186acb0 <col:17> 'struct header *' lvalue Var 0x186a950 'h' 'struct header *'
*/
/* (3)
|   |-BinaryOperator 0x132a068 <line:69:5, col:30> 'int' '='
|   | |-DeclRefExpr 0x1329f68 <col:5> 'int' lvalue Var 0x1329d38 'value' 'int'
|   | `-ImplicitCastExpr 0x132a050 <col:13, col:30> 'int' <LValueToRValue>
|   |   `-MemberExpr 0x132a020 <col:13, col:30> 'int' lvalue .value 0x1328f88
|   |     `-MemberExpr 0x1329ff0 <col:13, col:23> 'struct (unnamed struct at bad.c:55:9)':'struct header::(unnamed at bad.c:55:9)' lvalue .nested 0x1329038
|   |       `-MemberExpr 0x1329fc0 <col:13, col:16> 'struct (unnamed struct at bad.c:53:5)':'struct header::(unnamed at bad.c:53:5)' lvalue ->nested 0x13290e8
|   |         `-ImplicitCastExpr 0x1329fa8 <col:13> 'struct header *' <LValueToRValue>
|   |           `-DeclRefExpr 0x1329f88 <col:13> 'struct header *' lvalue Var 0x1329b70 'h' 'struct header *'
*/
/*
|-RecordDecl 0x812e58 <line:202:1, line:205:1> line:202:8 struct pair2 definition
| |-FieldDecl 0x812f20 <line:203:5, col:17> col:17 referenced a 'struct pair':'struct pair'
| `-FieldDecl 0x812f90 <line:204:5, col:17> col:17 b 'struct pair':'struct pair'
*/
  auto capture_record_type = hasDescendant(declRefExpr(to(anyOf(
      varDecl(unless(isRegister()), hasTypeLoc(typeLoc().bind("record_type"))),
      recordDecl(namedDecl().bind("record_type")),
      parmVarDecl(hasTypeLoc(typeLoc().bind("record_type")))
    ))).bind("record"));

  auto capture_assign_operator = binaryOperator(
      anyOf(
        isAssignmentOperator(),
        hasAnyOperatorName("+=", "-=")
      )
    );

  auto is_not_in_case = unless(hasAncestor(caseStmt()));
  auto is_not_in_initlistexpr = unless(hasAncestor(initListExpr()));
  auto is_not_in_vardecl = unless(hasAncestor(varDecl()));
  auto is_not_in_static_vardecl = unless(hasAncestor(varDecl(allOf(isStaticLocal(), isStaticStorageClass()))));
  auto is_not_in_const_vardecl = unless(hasAncestor(varDecl(hasConstantInitialization())));
  auto is_not_in_global_vardecl = hasAncestor(functionDecl());
  auto is_not_in_array_vardecl = unless(hasAncestor(varDecl(hasType(arrayType())))); // e.g. int array[1+2]
  auto is_not_in_fielddecl = unless(hasAncestor(fieldDecl()));
  auto is_binary_operator = hasAncestor(binaryOperator(unless(isAssignmentOperator())));
  auto is_not_in_enum = unless(hasAncestor(enumConstantDecl()));
  auto is_not_increment = allOf(
        unless(hasAncestor(unaryOperator(hasOperatorName("++")))),
        unless(hasAncestor(unaryOperator(hasOperatorName("--"))))
      );
  // auto is_not_increment = unless(hasAncestor(unaryOperator(hasAnyOperatorName("++", "--"))));
  auto is_bitfield = hasDeclaration(
        fieldDecl(isBitField(), unless(hasIntBitwidth()))
      );
  auto is_not_pointer_operation = allOf(
        // unless(hasAncestor(arraySubscriptExpr())),
        unless(hasAncestor(unaryOperator(hasOperatorName("*")))), // allOf() を残すための重複行
        unless(hasAncestor(unaryOperator(hasOperatorName("*"))))
      );
  auto child_does_not_have_record = unless(hasAncestor(memberExpr()));

  auto add_include = addInclude("trace.h", IncludeFormat::Angled);
  // auto add_include = addInclude("trace.h"); // Avoids "config.h:7:4: error: #error config.h must be #included before system headers"

  auto change_variable = [add_include](auto macro_name, auto variable_id, auto type_id) {
    return editList({
        insertBefore(
          node(variable_id), 
          cat(macro_name, "(")
        ),
        insertAfter(
          node(variable_id), 
          cat(", ", node(variable_id), ", (", describe(type_id), "))")
        ),
        add_include,
    });
  };

/* (a) 
|   |-DeclStmt 0x1b86a20 <line:105:5, col:19>
|   | `-VarDecl 0x1b869b8 <col:5, col:18> col:18 used i 'int' register
*/

  // <VarDecl <ArraySubscriptExpr>>
/*
|   |-DeclStmt 0x1650218 <line:83:5, col:30>
|   | `-VarDecl 0x1650120 <col:5, col:29> col:18 x 'unsigned int' cinit
|   |   `-ImplicitCastExpr 0x1650200 <col:22, col:29> 'unsigned int' <LValueToRValue>
|   |     `-ArraySubscriptExpr 0x16501e0 <col:22, col:29> 'unsigned int' lvalue
|   |       |-ImplicitCastExpr 0x16501c8 <col:22> 'unsigned int *' <ArrayToPointerDecay>
|   |       | `-DeclRefExpr 0x1650188 <col:22> 'unsigned int[3]' lvalue Var 0x164fea0 'array' 'unsigned int[3]'
|   |       `-IntegerLiteral 0x16501a8 <col:28> 'int' 1
*/
/*
|   | |-MemberExpr 0x1a1c620 <col:2, col:9> 'uint64':'unsigned long' lvalue .tdir_count 0x18cebf0
|   | | `-ArraySubscriptExpr 0x1a1c600 <col:2, col:7> 'TIFFDirEntry':'TIFFDirEntry' lvalue
|   | |   |-ImplicitCastExpr 0x1a1c5d0 <col:2> 'TIFFDirEntry *' <LValueToRValue>
|   | |   | `-DeclRefExpr 0x1a1c590 <col:2> 'TIFFDirEntry *' lvalue ParmVar 0x1a1ae70 'dir' 'TIFFDirEntry *'
|   | |   `-ImplicitCastExpr 0x1a1c5e8 <col:6> 'uint32':'unsigned int' <LValueToRValue>
|   | |     `-DeclRefExpr 0x1a1c5b0 <col:6> 'uint32':'unsigned int' lvalue Var 0x1a1b3a0 'm' 'uint32':'unsigned int'
*/
/*
|   |   `-ImplicitCastExpr 0x815a38 <col:13, col:23> 'int' <LValueToRValue>
|   |     `-ArraySubscriptExpr 0x815a18 <col:13, col:23> 'int' lvalue
|   |       |-ImplicitCastExpr 0x815a00 <col:13, col:16> 'int *' <ArrayToPointerDecay>
|   |       | `-MemberExpr 0x8159b0 <col:13, col:16> 'int[3]' lvalue ->array 0x813430
|   |       |   `-ImplicitCastExpr 0x815998 <col:13> 'struct header *' <LValueToRValue>
|   |       |     `-DeclRefExpr 0x815978 <col:13> 'struct header *' lvalue Var 0x814570 'h' 'struct header *'
|   |       `-IntegerLiteral 0x8159e0 <col:22> 'int' 0
*/
  auto HandleRvalueArraySubscriptExpr = makeRule(
      arraySubscriptExpr(
        is_rvalue,
        unless(is_referenced_value),
        is_not_in_initlistexpr,
        child_does_not_have_record,
        hasBase(capture_record_type),
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue"),
      {
        changeTo(
          before(node("rvalue")),
          cat("__trace_member_rvalue(")
        ),
        changeTo(
          after(node("rvalue")),
          cat(", ", node("rvalue"), ", (", describe("rvalue_type"), "), ", node("record"), ", (", name("record_type"), "))")
        ),
        add_include,
      },
      declaration_found("HandleRvalueArraySubscriptExpr")
    );

  auto HandleRvalueMemberExprArraySubscriptExpr = makeRule(
      arraySubscriptExpr(
        is_rvalue,
        unless(is_referenced_value),
        is_not_in_initlistexpr,
        child_does_not_have_record,
        hasBase(ignoringParenImpCasts(memberExpr(member(has(typeLoc().bind("record_type")))).bind("record"))),
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue"),
      {
        changeTo(
          before(node("rvalue")),
          cat("__trace_member_rvalue(")
        ),
        changeTo(
          after(node("rvalue")),
          cat(", ", node("rvalue"), ", (", describe("rvalue_type"), "), ", node("record"), ", (", name("record_type"), "))")
        ),
        add_include,
      },
      declaration_found("HandleRvalueMemberExprArraySubscriptExpr")
    );

/*
|   `-DeclStmt 0x1c57fe0 <line:82:5, col:23>
|     `-VarDecl 0x1c57ee8 <col:5, col:22> col:10 y 'int *' cinit
|       `-UnaryOperator 0x1c57fc8 <col:14, col:22> 'int *' prefix '&' cannot overflow
|         `-ArraySubscriptExpr 0x1c57fa8 <col:15, col:22> 'int' lvalue
|           |-ImplicitCastExpr 0x1c57f90 <col:15> 'int *' <ArrayToPointerDecay>
|           | `-DeclRefExpr 0x1c57f50 <col:15> 'int[3]' lvalue Var 0x1c57ba0 'array' 'int[3]'
|           `-IntegerLiteral 0x1c57f70 <col:21> 'int' 0
*/
  auto HandleLvalueArraySubscriptExpr = makeRule(
      arraySubscriptExpr(
        // is_lvalue,
        is_not_in_static_vardecl,
        is_not_in_global_vardecl,
        is_not_in_const_vardecl,
        is_not_in_initlistexpr,
        is_not_increment,
        child_does_not_have_record,
        hasBase(capture_record_type),
        hasType(qualType().bind("lvalue_type"))
      ).bind("lvalue"),
      {
        changeTo(
          before(node("lvalue")),
          cat("__trace_member_lvalue(")
        ),
        changeTo(
          after(node("lvalue")),
          cat(", ", node("lvalue"), ", (", describe("lvalue_type"), "), ", node("record"), ", (", name("record_type"), "))")
        ),
        add_include,
      },
      declaration_found("HandleLvalueArraySubscriptExpr")
    );

  auto HandleLvalueMemberExprArraySubscriptExpr = makeRule(
      arraySubscriptExpr(
        // is_lvalue,
        is_not_in_static_vardecl,
        is_not_in_global_vardecl,
        is_not_in_const_vardecl,
        is_not_in_initlistexpr,
        is_not_increment,
        child_does_not_have_record,
        hasType(qualType().bind("lvalue_type")),
        hasBase(ignoringParenImpCasts(memberExpr(member(has(typeLoc().bind("record_type")))).bind("record")))
      ).bind("lvalue"),
      {
        changeTo(
          before(node("lvalue")),
          cat("__trace_member_lvalue(")
        ),
        changeTo(
          after(node("lvalue")),
          cat(", ", node("lvalue"), ", (", describe("lvalue_type"), "), ", node("record"), ", (", name("record_type"), "))")
        ),
        add_include,
      },
      declaration_found("HandleLvalueMemberExprArraySubscriptExpr")
    );

  // <VarDecl <CallExpr>>
/*
|   |-DeclStmt 0xa18ee0 <line:34:5, col:17>
|   | `-VarDecl 0xa18df8 <col:5, col:16> col:9 used x 'int' cinit
|   |   `-CallExpr 0xa18eb8 <col:13, col:16> 'int'
|   |     |-ImplicitCastExpr 0xa18ea0 <col:13> 'int (*)(int)' <FunctionToPointerDecay>
|   |     | `-DeclRefExpr 0xa18e60 <col:13> 'int (int)' Function 0xa176e0 'f' 'int (int)'
|   |     `-IntegerLiteral 0xa18e80 <col:15> 'int' 1
*/
  auto HandleVarDecl = makeRule(
      varDecl(
        isExpansionInMainFile(), // "Invalid argument Range is in system header" 防止
        unless(isExpansionInSystemHeader()),
        unless(hasParent(cxxForRangeStmt())),
        unless(hasParent(declStmt(hasParent(ifStmt())))),
        hasDescendant(expr()), // 代入を伴うこと
        hasParent(declStmt( // 文法破壊防止
          unless(hasParent(forStmt())),
          unless(hasParent(cxxForRangeStmt())),
          hasSingleDecl(varDecl())
        ).bind("DeclStmt")),
        hasTypeLoc(typeLoc().bind("lvalue_type"))
      ).bind("lvalue"),
      {
        insertAfter(
          node("DeclStmt"),
          cat(" __trace_variable_declaration(", name("lvalue"), ", (", node("lvalue_type"), "));")
        ),
        add_include,
      },
      declaration_found("HandleVarDecl")
    );

  // <AssignOperator <DeclRefExpr> <???>>
  // lvalue をハンドルするのみ
/* int a = (_p = &p)->a;
|   |-DeclStmt 0x8e0750 <line:208:5, col:25>
|   | `-VarDecl 0x8e0608 <col:5, col:24> col:9 a 'int' cinit
|   |   `-ImplicitCastExpr 0x8e0738 <col:13, col:24> 'int' <LValueToRValue>
|   |     `-MemberExpr 0x8e0708 <col:13, col:24> 'int' lvalue ->a 0x8df918
|   |       `-ParenExpr 0x8e06e8 <col:13, col:21> 'struct pair *'
|   |         `-BinaryOperator 0x8e06c8 <col:14, col:20> 'struct pair *' '='
|   |           |-DeclRefExpr 0x8e0670 <col:14> 'struct pair *' lvalue Var 0x8e0570 '_p' 'struct pair *'
|   |           `-UnaryOperator 0x8e06b0 <col:19, col:20> 'struct pair *' prefix '&' cannot overflow
|   |             `-DeclRefExpr 0x8e0690 <col:20> 'struct pair':'struct pair' lvalue Var 0x8dfca0 'p' 'struct pair':'struct pair'
*/
  auto HandleLvalueDeclRefExpr = makeRule(
      declRefExpr(
        unless(isInMacro()),
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_lvalue,
        is_not_in_static_vardecl,
        is_not_in_const_vardecl,
        is_not_in_initlistexpr,
        is_not_increment,
        is_not_pointer_operation,
        to(varDecl(
          /* (a) */ unless(isRegister()),
          hasTypeLoc(typeLoc().bind("lvalue_type"))
        ))
      ).bind("lvalue"),
      {
        insertBefore(
          node("lvalue"), 
          cat("__trace_variable_lvalue(")
        ),
        insertAfter(
          node("lvalue"), 
          cat(", ", node("lvalue"), ", (", node("lvalue_type"), "))")
        ),
        add_include,
      },
      assignment_found("HandleLvalueDeclRefExpr")
    );

  // <MemberExpr> = <???>
  // lvalue をハンドルするのみ
/* (1)
|   |-BinaryOperator 0x16388f8 <line:126:5, col:20> 'unsigned int' '='
|   | |-MemberExpr 0x1638890 <col:5, col:13> 'unsigned int' lvalue bitfield .left 0x1638690
|   | | `-DeclRefExpr 0x1638870 <col:5> 'struct bit_counter':'struct bit_counter' lvalue Var 0x16387f0 'counter' 'struct bit_counter':'struct bit_counter'
|   | `-ImplicitCastExpr 0x16388e0 <col:20> 'unsigned int' <IntegralCast>
|   |   `-IntegerLiteral 0x16388c0 <col:20> 'int' 1
*/
/* (2)
|   `-BinaryOperator 0x18c6d78 <line:125:5, col:32> 'int' '='
|     |-MemberExpr 0x18c6d28 <col:5, col:23> 'int' lvalue .length 0x18bf958
|     | `-MemberExpr 0x18c6cf8 <col:5, col:16> 'struct (unnamed struct at bad.c:92:5)':'struct header::(unnamed at bad.c:92:5)' lvalue ->nested 0x18bfbc8
|     |   `-ImplicitCastExpr 0x18c6ce0 <col:5, col:8> 'struct header *' <LValueToRValue>
|     |     `-MemberExpr 0x18c6cb0 <col:5, col:8> 'struct header *' lvalue ->header 0x18bfcd0
|     |       `-ImplicitCastExpr 0x18c6c98 <col:5> 'struct header *' <LValueToRValue>
|     |         `-DeclRefExpr 0x18c6c78 <col:5> 'struct header *' lvalue Var 0x18c0498 'h' 'struct header *'
|     `-IntegerLiteral 0x18c6d58 <col:32> 'int' 3
*/
/* C++ のクラスメンバー
| |   |-BinaryOperator 0x2ab7da8 <line:35:9, col:15> 'int' lvalue '='
| |   | |-MemberExpr 0x2ab7d58 <col:9> 'int' lvalue ->ceo 0x2ab7bc8
| |   | | `-CXXThisExpr 0x2ab7d48 <col:9> 'Company *' implicit this
| |   | `-IntegerLiteral 0x2ab7d88 <col:15> 'int' 1
*/
/* 除外パターン：テンプレート引数のクラス名
class Rectangle {
  [...]
};
[...]
    auto rect = std::make_unique<Rectangle>(0, 0, 0, 0);
                                 ~~~~~~~~~
    [... rect の参照 ...]
*/
  auto capture_member_lvalue = hasLHS( // // NOTE: TK_IgnoreUnlessSpelledInSource を使うとRValueへのimplicit castが見えなくなるので hasLHS を使わざるを得ない。
      memberExpr(
        unless(isInMacro()),
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_not_in_initlistexpr,
        is_not_increment,
        unless(is_bitfield), // TODO: bit field はトレース対象外なのはなんとかしたいな
        is_not_pointer_operation,
        unless(hasAncestor(memberExpr())),
        anyOf(
          capture_record_type,
          has(cxxThisExpr(hasType(qualType().bind("class_type"))).bind("class"))
        ),
        hasType(qualType().bind("lvalue_type"))
      ).bind("lvalue"));
  auto HandleLvalueMemberExpr = makeRule(
      traverse(TK_IgnoreUnlessSpelledInSource, expr(anyOf(
        binaryOperator(
          hasOperatorName("="), 
          capture_member_lvalue
        ),
        cxxOperatorCallExpr(
          hasOperatorName("="), 
          capture_member_lvalue
        )
      ))),
      {
        insertBefore(
          node("lvalue"),
          cat("__trace_member_lvalue(")
        ),
        insertAfter(
          node("lvalue"),
          cat(", ", node("lvalue"), ", (", describe("lvalue_type"), "), ", selectBound({
            { "record", cat(node("record"), ", (", name("record_type")) }, 
            { "class", cat(node("class"), ", (", describe("class_type")) }
          }), "))")
        ),
        add_include,
      },
      assignment_found("HandleLvalueMemberExpr")
    );

/*
|   |   `-CallExpr 0x14f1448 <col:13, col:33> 'int'
|   |     |-ImplicitCastExpr 0x14f1430 <col:13> 'int (*)(int)' <FunctionToPointerDecay>
|   |     | `-DeclRefExpr 0x14f1290 <col:13> 'int (int)' Function 0x14eab58 'f' 'int (int)'
*/
/*
|   |   | |   `-UnaryOperator 0x235f138 <col:14, col:33> 'unsigned int' lvalue prefix '*' cannot overflow
|   |   | |     `-CStyleCastExpr 0x235f110 <col:15, col:33> 'unsigned int *' <BitCast>
|   |   | |       `-UnaryOperator 0x235f0b8 <col:32, col:33> 'unsigned short *' prefix '&' cannot overflow
|   |   | |         `-DeclRefExpr 0x235f068 <col:33> 'unsigned short' lvalue Var 0x235efb0 's' 'unsigned short'
*/
/* `for (auto i : array) {}`
|   `-CXXForRangeStmt 0x1508ec0 <line:17:5, line:19:5>
|     |-<<<NULL>>>
|     |-DeclStmt 0x1507830 <line:17:19>
|     | `-VarDecl 0x15075a0 <col:19> col:19 implicit used __range1 'int (&)[3]' cinit
|     |   `-DeclRefExpr 0x1507420 <col:19> 'int[3]' lvalue Var 0x1507230 'array' 'int[3]'
|     |-DeclStmt 0x1507c20 <col:17>
|     | `-VarDecl 0x15078c8 <col:17> col:17 implicit used __begin1 'int *':'int *' cinit
|     |   `-ImplicitCastExpr 0x1507af0 <col:17> 'int *' <ArrayToPointerDecay>
|     |     `-DeclRefExpr 0x1507848 <col:17> 'int[3]' lvalue Var 0x15075a0 '__range1' 'int (&)[3]'
|     |-DeclStmt 0x1507c38 <col:17>
|     | `-VarDecl 0x1507970 <col:17, col:19> col:17 implicit used __end1 'int *':'int *' cinit
|     |   `-BinaryOperator 0x1507b40 <col:17, col:19> 'int *' '+'
|     |     |-ImplicitCastExpr 0x1507b28 <col:17> 'int *' <ArrayToPointerDecay>
|     |     | `-DeclRefExpr 0x1507868 <col:17> 'int[3]' lvalue Var 0x15075a0 '__range1' 'int (&)[3]'
|     |     `-IntegerLiteral 0x1507b08 <col:19> 'long' 3
|     |-BinaryOperator 0x1507cc0 <col:17> 'bool' '!='
|     | |-ImplicitCastExpr 0x1507c90 <col:17> 'int *':'int *' <LValueToRValue>
|     | | `-DeclRefExpr 0x1507c50 <col:17> 'int *':'int *' lvalue Var 0x15078c8 '__begin1' 'int *':'int *'
|     | `-ImplicitCastExpr 0x1507ca8 <col:17> 'int *':'int *' <LValueToRValue>
|     |   `-DeclRefExpr 0x1507c70 <col:17> 'int *':'int *' lvalue Var 0x1507970 '__end1' 'int *':'int *'
|     |-UnaryOperator 0x1507d00 <col:17> 'int *':'int *' lvalue prefix '++'
|     | `-DeclRefExpr 0x1507ce0 <col:17> 'int *':'int *' lvalue Var 0x15078c8 '__begin1' 'int *':'int *'
|     |-DeclStmt 0x1507518 <col:10, col:24>
|     | `-VarDecl 0x15074b0 <col:10, col:17> col:15 i 'int':'int' cinit
|     |   `-ImplicitCastExpr 0x1507e50 <col:17> 'int' <LValueToRValue>
|     |     `-UnaryOperator 0x1507d50 <col:17> 'int' lvalue prefix '*' cannot overflow
|     |       `-ImplicitCastExpr 0x1507d38 <col:17> 'int *':'int *' <LValueToRValue>
|     |         `-DeclRefExpr 0x1507d18 <col:17> 'int *':'int *' lvalue Var 0x15078c8 '__begin1' 'int *':'int *'
|     `-CompoundStmt 0x1508f20 <col:26, line:19:5>
*/
/* 除外(1)：
|   `-IfStmt 0x2eac4b0 <line:155:5, col:40> has_var
|     |-DeclStmt 0x2eac4d8 <col:9, col:36>
|     | `-VarDecl 0x2eac190 <col:9, col:36> col:21 used res 'const Object *' cinit
|     |   `-ImplicitCastExpr 0x2eac438 <col:27, col:36> 'const Object *' <NoOp>
|     |     `-CallExpr 0x2eac2a0 <col:27, col:36> 'Object *'
|     |       `-ImplicitCastExpr 0x2eac288 <col:27> 'Object *(*)()' <FunctionToPointerDecay>
|     |         `-DeclRefExpr 0x2eac240 <col:27> 'Object *()' lvalue Function 0x2d683e8 'test_new' 'Object *()'
|     |-ImplicitCastExpr 0x2eac488 <col:21> 'bool' <PointerToBoolean>
|     | `-ImplicitCastExpr 0x2eac470 <col:21> 'const Object *' <LValueToRValue>
|     |   `-DeclRefExpr 0x2eac450 <col:21> 'const Object *' lvalue Var 0x2eac190 'res' 'const Object *' // => 除外
|     `-CompoundStmt 0x2eac4a0 <col:39, col:40>
*/
/* 除外(2)：`makeStream(std::move(obj)`
|   |   |   |   |         `-CXXMemberCallExpr 0x204ea70 <col:40, col:138> 'Stream *'
|   |   |   |   |           |-MemberExpr 0x204e7c8 <col:40> '<bound member function type>' ->makeStream 0x1c4c0e8
|   |   |   |   |           | `-CXXThisExpr 0x204e7b8 <col:40> 'Parser *' implicit this
|   |   |   |   |           |-CallExpr 0x204e910 <col:51, col:64> 'typename std::remove_reference<Object &>::type':'Object' xvalue
|   |   |   |   |           | |-ImplicitCastExpr 0x204e8f8 <col:51, col:56> 'typename std::remove_reference<Object &>::type &&(*)(Object &) noexcept' <FunctionToPointerDecay>
|   |   |   |   |           | | `-DeclRefExpr 0x204e8c0 <col:51, col:56> 'typename std::remove_reference<Object &>::type &&(Object &) noexcept' lvalue Function 0x1b40c78 'move' 'typename std::remove_reference<Object &>::type &&(Object &) noexcept' (FunctionTemplate 0xd6c8a8 'move')
*/

  // <???> = <DeclRefExpr>;
  // rvalue をハンドルするのみ
  auto HandleRvalueDeclRefExpr = makeRule(
      declRefExpr(
        unless(isInMacro()),
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_rvalue,
        is_not_in_static_vardecl,
        is_not_in_global_vardecl,
        is_not_in_const_vardecl,
        is_not_in_initlistexpr,
        is_not_increment,
        unless(is_referenced_value),
        hasParent(implicitCastExpr(unless(hasCastKind(CK_FunctionToPointerDecay)))), // 除外(2)
        unless(hasAncestor(lambdaExpr())), // NOTE: ラムダ式 [](...){} のかっこ内は計装対象外
        child_does_not_have_record,
        unless(hasAncestor(cxxForRangeStmt())),
        hasAncestor(compoundStmt()),
        anyOf(
          to(varDecl(
            unless(isRegister()), 
            hasParent(declStmt(unless(hasParent(ifStmt())))) // 除外(1)
          )),
          to(parmVarDecl())
          // to(functionDecl()) // NOTE: 除外(2)ができないので一旦除外
        ),
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue"),
      change_variable("__trace_variable_rvalue", "rvalue", "rvalue_type"),
      assignment_found("HandleRvalueDeclRefExpr")
    );

  // <???> = <IntegerLiteral>
  // <???> ?= <IntegerLiteral>
  // rvalue をハンドルするのみ
/*
|   |-BinaryOperator 0x20156d0 <line:45:5, col:12> 'int' '='
|   | |-MemberExpr 0x2015680 <col:5, col:8> 'int' lvalue ->b 0x20104c0
|   | | `-ImplicitCastExpr 0x2015668 <col:5> 'struct pair *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x2015648 <col:5> 'struct pair *' lvalue Var 0x2014300 'q' 'struct pair *'
|   | `-IntegerLiteral 0x20156b0 <col:12> 'int' 1
*/
/*
|   |-BinaryOperator 0x1381a28 <line:27:5, col:9> 'unsigned int' '='
|   | |-DeclRefExpr 0x13819d0 <col:5> 'unsigned int' lvalue Var 0x1381820 'z' 'unsigned int'
|   | `-ImplicitCastExpr 0x1381a10 <col:9> 'unsigned int' <IntegralCast>
|   |   `-IntegerLiteral 0x13819f0 <col:9> 'int' 0
*/
/*
|   |   `-CStyleCastExpr 0x1bc1788 <col:10, col:18> 'void *' <NullToPointer>
|   |     `-IntegerLiteral 0x1bc1750 <col:18> 'int' 0
*/
/* 除外するケース： `XRef::XRef() : objStrs { 5 }`
|-CXXConstructorDecl 0x387bd38 parent 0x382ca18 prev 0x382cc00 <line:234:1, line:254:1> line:234:7 used XRef 'void ()'
[...]
| |-CXXCtorInitializer Field 0x3861e30 'objStrs' 'PopplerCache<Goffset, ObjectStream>':'PopplerCache<long long, ObjectStream>'
| | `-CXXConstructExpr 0x387bef8 <col:16, col:28> 'PopplerCache<Goffset, ObjectStream>':'PopplerCache<long long, ObjectStream>' 'void (std::size_t)' list
| |   `-ImplicitCastExpr 0x387beb8 <col:26> 'std::size_t':'unsigned long' <IntegralCast>
| |     `-IntegerLiteral 0x387be20 <col:26> 'int' 5
[...]
| `-CompoundStmt 0x387cfa8 <line:235:1, line:254:1>
*/
  // FIXME: マイナス値が -(____trace_variable_rvalue(1, const int)) になってしまう。
  auto change_rvalue_const_int = change_variable("__trace_variable_rvalue", "rvalue", "rvalue_type");

  auto HandleRvalueIntegerLiteral = makeRule(
      // TODO: v += u を v = v + u に正規化
      // NOTE: std::array<std::pair<int, int>, 2> の数字にマッチしないように、トラバースのモードを変更する必要あり
      traverse(TK_IgnoreUnlessSpelledInSource, integerLiteral(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_not_in_case,
        is_not_in_initlistexpr,
        is_not_in_static_vardecl,
        is_not_in_global_vardecl,
        is_not_in_array_vardecl,
        is_not_in_fielddecl,
        is_not_in_enum,
        unless(hasParent(cStyleCastExpr(hasCastKind(CK_NullToPointer)))),
        unless(hasAncestor(varDecl(hasAlignedAttr()))),
        unless(hasAncestor(parmVarDecl())),
        hasAncestor(compoundStmt()), // NOTE: unless(hasAncestor(cxxCtorInitializer())) が発火しないので、代替
        anyOf(
          hasParent(explicitCastExpr()),
          hasParent(implicitCastExpr()),
          hasParent(arraySubscriptExpr()),
          hasParent(callExpr()),
          hasParent(returnStmt()),
          hasParent(binaryOperator())
        ), // NOTE: (int (*)[3]) malloc(sizeof(int[3])) の明示キャストとマッチさせない
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue")),
      change_rvalue_const_int,
      assignment_found("HandleRvalueIntegerLiteral")
    );
    
  auto HandleRvalueSizeofExpr = makeRule(
      sizeOfExpr(expr(
        is_not_in_case,
        is_not_in_initlistexpr,
        is_not_in_static_vardecl,
        is_not_in_global_vardecl,
        is_not_in_array_vardecl,
        is_not_in_fielddecl,
        is_not_in_enum
      )).bind("rvalue"),
      change_rvalue_const_int,
      assignment_found("HandleRvalueSizeofExpr")
    );

/*
|     |-ImplicitCastExpr 0x81c338 <col:12> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x81c320 <col:12> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x81c258 <col:12> 'char[8]' lvalue "z = %d\n"
*/
  auto HandleRvalueStringLiteral = makeRule(
      expr(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        stringLiteral(
          is_not_in_static_vardecl,
          is_not_in_array_vardecl,
          is_not_in_fielddecl,
          hasType(type().bind("rvalue_type"))
        )
      ).bind("rvalue"),
      change_variable("__trace_variable_rvalue", "rvalue", "rvalue_type"),
      assignment_found("HandleRvalueStringLiteral")
    );

/*
|   |-DeclStmt 0x157a5c8 <line:119:5, col:21>
|   | `-VarDecl 0x157a4c0 <col:5, col:20> col:11 used x 'void *' cinit
|   |   `-ParenExpr 0x157a5a8 <col:15, col:20> 'void *'
|   |     `-ParenExpr 0x157a588 </usr/lib/llvm-14/lib/clang/14.0.5/include/stddef.h:89:16, col:25> 'void *'
|   |       `-CStyleCastExpr 0x157a560 <col:17, col:24> 'void *' <NullToPointer>
|   |         `-IntegerLiteral 0x157a528 <col:24> 'int' 0
*/
  auto HandleRvalueNull = makeRule(
      parenExpr(
        unless(isInMacro()),
        is_not_in_static_vardecl,
        is_not_in_global_vardecl,
        is_not_in_const_vardecl,
        is_not_in_initlistexpr,
        // NOTE: libtooling では，システム定義側に何かが挟まっているっぽい
        // NOTE: `((NULL))` みたいになっているとバグりそう
        hasDescendant(
          cStyleCastExpr(
            hasCastKind(CK_NullToPointer)
          )
        )
      ).bind("rvalue"),
      {
        insertBefore(
          node("rvalue"), 
          cat("__trace_variable_rvalue(")
        ),
        insertAfter(
          node("rvalue"), 
          cat(", ", node("rvalue"), ", (NULL))")
        ),
        add_include,
      },
      assignment_found("HandleRvalueNull")
    );

/*
| |   `-DeclStmt 0x1e399c8 <line:54:9, col:26>
| |     `-VarDecl 0x1e39950 <col:9, col:22> col:18 a 'Company *' cinit
| |       `-CXXThisExpr 0x1e399b8 <col:22> 'Company *' this
*/
/* 除外：
| |   |-BinaryOperator 0x2dd0fe8 <line:44:9, col:15> 'int' lvalue '='
| |   | |-MemberExpr 0x2dd0f98 <col:9> 'int' lvalue ->ceo 0x2dd0e08
| |   | | `-CXXThisExpr 0x2dd0f88 <col:9> 'Company *' implicit this
| |   | `-IntegerLiteral 0x2dd0fc8 <col:15> 'int' 1
*/
  auto HandleRvalueCXXThisExpr = makeRule(
      cxxThisExpr(
        is_rvalue,
        unless(hasAncestor(memberExpr())),
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue"),
      change_variable("__trace_variable_rvalue", "rvalue", "rvalue_type"),
      assignment_found("HandleRvalueCXXThisExpr")
  );

/*
|   |-DeclStmt 0x1e372a8 <line:9:5, col:37>
|   | `-VarDecl 0x1db6148 <col:5, col:30> col:26 a 'std::unique_ptr<int>':'std::unique_ptr<int>' cinit destroyed
|   |   `-ExprWithCleanups 0x1e37290 <col:26, col:30> 'std::unique_ptr<int>':'std::unique_ptr<int>'
|   |     `-CXXConstructExpr 0x1e37260 <col:26, col:30> 'std::unique_ptr<int>':'std::unique_ptr<int>' 'void (std::unique_ptr<int> &&) noexcept' elidable
|   |       `-MaterializeTemporaryExpr 0x1e37248 <col:30> 'std::unique_ptr<int>':'std::unique_ptr<int>' xvalue
|   |         `-CXXBindTemporaryExpr 0x1e2a000 <col:30> 'std::unique_ptr<int>':'std::unique_ptr<int>' (CXXTemporary 0x1e2a000)
|   |           `-ImplicitCastExpr 0x1e29fe0 <col:30> 'std::unique_ptr<int>':'std::unique_ptr<int>' <ConstructorConversion>
|   |             `-CXXConstructExpr 0x1e29fb0 <col:30> 'std::unique_ptr<int>':'std::unique_ptr<int>' 'void (std::nullptr_t) noexcept'
|   |               `-CXXNullPtrLiteralExpr 0x1db61b0 <col:30> 'std::nullptr_t'
*/
  auto HandleRvalueCXXNullPtrLiteralExpr = makeRule(
      cxxNullPtrLiteralExpr(
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue"),
      change_variable("__trace_variable_rvalue", "rvalue", "rvalue_type"),
      assignment_found("HandleRvalueCXXNullPtrLiteralExpr")
  );

/*
|   `-DeclStmt 0x1e373c0 <line:10:5, col:26>
|     `-VarDecl 0x1e372d0 <col:5, col:21> col:10 b 'bool' cinit
|       `-ImplicitCastExpr 0x1e373a8 <col:14, col:21> 'bool' <IntegralToBoolean>
|         `-BinaryOperator 0x1e37388 <col:14, col:21> 'int' '|'
|           |-ImplicitCastExpr 0x1e37358 <col:14> 'int' <IntegralCast>
|           | `-CXXBoolLiteralExpr 0x1e37338 <col:14> 'bool' true
|           `-ImplicitCastExpr 0x1e37370 <col:21> 'int' <IntegralCast>
|             `-CXXBoolLiteralExpr 0x1e37348 <col:21> 'bool' false
*/
  auto HandleRvalueCXXBoolLiteralExpr = makeRule(
      cxxBoolLiteral(
        hasType(qualType().bind("rvalue_type"))
      ).bind("rvalue"),
      change_variable("__trace_variable_rvalue", "rvalue", "rvalue_type"),
      assignment_found("HandleRvalueCXXBoolLiteralExpr")
  );

  // <DeclRefExpr>++
/*
|     |-UnaryOperator 0xcbd3d0 <col:28, col:29> 'int' postfix '++'
|     | `-DeclRefExpr 0xcbd3b0 <col:28> 'int' lvalue Var 0xcbc1e8 'i' 'int'
*/
  // auto HandleLvalueRvalueIncrementDeclRefExpr = makeRule(
  //     unaryOperator(
  //       unless(isInMacro()),
  //       isExpansionInMainFile(),
  //       unless(isExpansionInSystemHeader()),
  //       is_lvalue,
  //       unless(hasAncestor(varDecl())),
  //       unless(hasAncestor(memberExpr())),
  //       is_not_pointer_operation,
  //       hasOperatorName("++"),
  //       declRefExpr(
  //         to(varDecl(
  //           /* (a) */ unless(isRegister()),
  //           hasTypeLoc(typeLoc().bind("lvalue_type"))
  //         ))
  //       ).bind("lvalue")
  //     ).bind("expr"),
  //     {
  //       changeTo(
  //         node("expr"),
  //         cat(
  //           "(__trace_variable_lvalue(", node("lvalue"), ", (", node("lvalue_type"), "))"
  //           " += ",
  //           "__trace_variable_rvalue(1, (const int)))"
  //         )
  //       ),
  //       add_include,
  //     },
  //     cat("(HandleLvalueRvalueIncrementDeclRefExpr)")
  //   );

  // <???> = <MemberExpr <DeclRefExpr>>
  // rvalue をハンドルするのみ
/*
|   `-BinaryOperator 0x1a9ea80 <line:47:5, col:15> 'int' '='
|     |-MemberExpr 0x1a9e9d0 <col:5, col:8> 'int' lvalue ->a 0x1a99528
|     | `-ImplicitCastExpr 0x1a9e9b8 <col:5> 'struct pair *' <LValueToRValue>
|     |   `-DeclRefExpr 0x1a9e998 <col:5> 'struct pair *' lvalue Var 0x1a9d3d0 'q' 'struct pair *'
|     `-ImplicitCastExpr 0x1a9ea68 <col:12, col:15> 'int' <LValueToRValue>
|       `-MemberExpr 0x1a9ea38 <col:12, col:15> 'int' lvalue ->b 0x1a99590
|         `-ImplicitCastExpr 0x1a9ea20 <col:12> 'struct pair *' <LValueToRValue>
|           `-DeclRefExpr 0x1a9ea00 <col:12> 'struct pair *' lvalue Var 0x1a9d3d0 'q' 'struct pair *'
*/
/*
|   |-BinaryOperator 0x18c6a90 <line:122:5, col:27> 'int' '='
|   | |-DeclRefExpr 0x18c6950 <col:5> 'int' lvalue Var 0x18c5df8 'x' 'int'
|   | `-ImplicitCastExpr 0x18c6a50 <col:9, col:27> 'int' <LValueToRValue>
|   |   `-MemberExpr 0x18c6a20 <col:9, col:27> 'int' lvalue .length 0x18bf958 // <- Want to match this!
|   |     `-MemberExpr 0x18c69f0 <col:9, col:20> 'struct (unnamed struct at bad.c:92:5)':'struct header::(unnamed at bad.c:92:5)' lvalue ->nested 0x18bfbc8
|   |       `-ImplicitCastExpr 0x18c69d8 <col:9, col:12> 'struct header *' <LValueToRValue>
|   |         `-MemberExpr 0x18c69a8 <col:9, col:12> 'struct header *' lvalue ->header 0x18bfcd0
|   |           `-ImplicitCastExpr 0x18c6990 <col:9> 'struct header *' <LValueToRValue>
|   |             `-DeclRefExpr 0x18c6970 <col:9> 'struct header *' lvalue Var 0x18c0498 'h' 'struct header *'
*/
/*
|   | `-VarDecl 0x815910 <col:5, col:23> col:9 a 'int' cinit
|   |   `-ImplicitCastExpr 0x815a38 <col:13, col:23> 'int' <LValueToRValue>
|   |     `-ArraySubscriptExpr 0x815a18 <col:13, col:23> 'int' lvalue
|   |       |-ImplicitCastExpr 0x815a00 <col:13, col:16> 'int *' <ArrayToPointerDecay>
|   |       | `-MemberExpr 0x8159b0 <col:13, col:16> 'int[3]' lvalue ->array 0x813430
|   |       |   `-ImplicitCastExpr 0x815998 <col:13> 'struct header *' <LValueToRValue>
|   |       |     `-DeclRefExpr 0x815978 <col:13> 'struct header *' lvalue Var 0x814570 'h' 'struct header *'
|   |       `-IntegerLiteral 0x8159e0 <col:22> 'int' 0
*/
/* `calc.add(c.ceo, c.cto);`
|   |-CXXMemberCallExpr 0x2ee9ce8 <line:59:5, col:26> 'int'
|   | |-MemberExpr 0x2ee9c18 <col:5, col:10> '<bound member function type>' .add 0x2ee78a0
|   | | `-DeclRefExpr 0x2ee9bf8 <col:5> 'Calculator' lvalue Var 0x2ee8c90 'calc' 'Calculator'
|   | |-ImplicitCastExpr 0x2ee9d18 <col:14, col:16> 'int' <LValueToRValue>
|   | | `-MemberExpr 0x2ee9c68 <col:14, col:16> 'int' lvalue .ceo 0x2ee86c0
|   | |   `-DeclRefExpr 0x2ee9c48 <col:14> 'Company' lvalue Var 0x2ee96b0 'c' 'Company'
|   | `-ImplicitCastExpr 0x2ee9d30 <col:21, col:23> 'int' <LValueToRValue>
|   |   `-MemberExpr 0x2ee9cb8 <col:21, col:23> 'int' lvalue .cto 0x2ee8728
|   |     `-DeclRefExpr 0x2ee9c98 <col:21> 'Company' lvalue Var 0x2ee96b0 'c' 'Company'
*/
/* 除外するケース：`char c = str.c_str()[2];`
|   `-DeclStmt 0x24c10d8 <line:33:5, col:28>
|     `-VarDecl 0x24c0f90 <col:5, col:27> col:10 c 'char' cinit
|       `-ImplicitCastExpr 0x24c10c0 <col:14, col:27> 'char':'char' <LValueToRValue>
|         `-ArraySubscriptExpr 0x24c10a0 <col:14, col:27> 'const char':'const char' lvalue
|           |-CXXMemberCallExpr 0x24c1048 <col:14, col:24> 'const char *'
|           | `-MemberExpr 0x24c1018 <col:14, col:18> '<bound member function type>' .c_str 0x1e1def0
|           |   `-ImplicitCastExpr 0x24c1068 <col:14> 'const std::basic_string<char>' lvalue <NoOp>
|           |     `-DeclRefExpr 0x24c0ff8 <col:14> 'std::string':'std::basic_string<char>' lvalue Var 0x24c0d28 'str' 'std::string':'std::basic_string<char>'
|           `-IntegerLiteral 0x24c1080 <col:26> 'int' 2
*/
  auto HandleRvalueFirstLevelMemberExpr = makeRule(
      memberExpr(
        unless(isInMacro()),
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_rvalue,
        is_not_in_initlistexpr,
        is_not_increment,
        is_not_pointer_operation,
        unless(is_bitfield),
        child_does_not_have_record,
        unless(hasParent(cxxMemberCallExpr())),
        member(valueDecl(hasType(qualType().bind("rvalue_type")))),
        anyOf(
          capture_record_type,
          has(cxxThisExpr(hasType(qualType().bind("class_type"))).bind("class"))
        )
      ).bind("rvalue"),
      {
        insertBefore(
          node("rvalue"),
          cat("__trace_member_rvalue(")
        ),
        insertAfter(
          node("rvalue"),
          cat(", ", node("rvalue"), ", (", describe("rvalue_type"), "), ", selectBound({
            { "record", cat(node("record"), ", (", name("record_type")) }, 
            { "class", cat(node("class"), ", (", describe("class_type")) }
          }), "))")
        ),
        add_include,
      },
      assignment_found("HandleRvalueFirstLevelMemberExpr")
    );

  auto HandleRvalueFirstAndSecondLevelMemberExpr = makeRule(
      memberExpr(
        unless(isInMacro()),
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_rvalue,
        unless(is_referenced_value),
        is_not_in_initlistexpr,
        is_not_increment,
        is_not_pointer_operation,
        unless(is_bitfield),
        child_does_not_have_record,
        member(fieldDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
        // NOTE: has() で囲わないと、Top LevelのmemberExprとマッチしてしまう
        has(ignoringParenImpCasts(
          memberExpr(
            member(fieldDecl(hasTypeLoc(typeLoc().bind("parent_type"))))
          ).bind("parent")
        ))
      ).bind("rvalue"),
      {
        insertBefore(
          node("rvalue"),
          cat("__trace_member_rvalue(")
        ),
        insertAfter(
          node("rvalue"),
          cat(", ", node("rvalue"), ", (", name("rvalue_type"), "), ", node("parent"), ", (", name("parent_type"), "))")
        ),
        add_include,
      },
      assignment_found("HandleRvalueFirstAndSecondLevelMemberExpr")
    );

  auto HandleRvalueSecondLevelMemberExpr = makeRule(
      memberExpr(ignoringParenImpCasts(
        memberExpr(
          unless(isInMacro()),
          isExpansionInMainFile(),
          unless(isExpansionInSystemHeader()),
          is_rvalue,
          unless(is_referenced_value),
          is_not_in_initlistexpr,
          is_not_increment,
          is_not_pointer_operation,
          unless(is_bitfield),
          member(fieldDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
          capture_record_type
        ).bind("rvalue")
      )),
      {
        insertBefore(
          node("rvalue"),
          cat("__trace_member_rvalue(")
        ),
        insertAfter(
          node("rvalue"),
          cat(", ", node("rvalue"), ", (", name("rvalue_type"), "), ", node("record"), ", (", name("record_type"), "))")
        ),
        add_include,
      },
      assignment_found("HandleRvalueSecondLevelMemberExpr")
    );

  auto HandleRvalueReferenceExpr = makeRule(
      unaryOperator(
        is_not_in_static_vardecl,
        is_not_in_const_vardecl,
        is_not_in_initlistexpr,
        hasOperatorName("&")
      ).bind("rvalue"),
      {
        insertBefore(
            node("rvalue"),
            cat("__trace_reference(")
          ),
        insertAfter(
            node("rvalue"),
            cat(", ", node("rvalue"), ")")
          ),
        add_include,
      },
      assignment_found("HandleRvalueReferenceExpr")
    );

  return applyFirst({
    // HandleTraceFunctionCall, // 無意味

    HandleVarDecl,

    // TODO: インクリメント、デクリメントのハンドルが甘い
    // HandleLvalueRvalueIncrementDeclRefExpr,

    // TODO: enum

    // TODO: *v などのポインタ操作をたどるトレース関数

    HandleLvalueMemberExprArraySubscriptExpr,
    HandleLvalueArraySubscriptExpr,
    HandleLvalueMemberExpr,
    HandleLvalueDeclRefExpr,

    HandleRvalueNull,
    HandleRvalueSizeofExpr,
    HandleRvalueCXXThisExpr,
    HandleRvalueCXXNullPtrLiteralExpr,
    HandleRvalueCXXBoolLiteralExpr,
    HandleRvalueReferenceExpr,
    HandleRvalueMemberExprArraySubscriptExpr,
    HandleRvalueArraySubscriptExpr,
    HandleRvalueFirstAndSecondLevelMemberExpr,
    HandleRvalueFirstLevelMemberExpr,
    HandleRvalueSecondLevelMemberExpr,
    HandleRvalueDeclRefExpr,
    HandleRvalueIntegerLiteral,
    HandleRvalueStringLiteral,
  });
}

VariableUpdateTracingCheck::VariableUpdateTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(VariableUpdateTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
