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

  auto is_rvalue = hasAncestor(implicitCastExpr(
      unless(hasParent(cStyleCastExpr(hasCastKind(CK_ToVoid)))),
      anyOf(
        hasCastKind(CK_LValueToRValue),
        hasCastKind(CK_ArrayToPointerDecay)
      )
    ));
  auto is_lvalue = allOf(
      isLValue(),
      unless(is_rvalue),
      unless(hasParent(whileStmt()))
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
        hasBase(capture_record_type)
        // hasType(type().bind("rvalue_type"))
      ).bind("rvalue"),
      {
        changeTo(
          before(node("rvalue")),
          cat("__trace_member_rvalue(")
        ),
        changeTo(
          after(node("rvalue")),
          cat(", ", node("rvalue"), ", (", "FIXME", "), ", node("record"), ", (", name("record_type"), "))")
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
        hasBase(ignoringParenImpCasts(memberExpr(member(has(typeLoc().bind("record_type")))).bind("record")))
        // hasTypeLoc(typeLoc().bind("rvalue_type"))
      ).bind("rvalue"),
      {
        changeTo(
          before(node("rvalue")),
          cat("__trace_member_rvalue(")
        ),
        changeTo(
          after(node("rvalue")),
          cat(", ", node("rvalue"), ", (", "FIXME", "), ", node("record"), ", (", name("record_type"), "))")
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
        hasBase(capture_record_type)
      ).bind("lvalue"),
      {
        changeTo(
          before(node("lvalue")),
          cat("__trace_member_lvalue(")
        ),
        changeTo(
          after(node("lvalue")),
          cat(", ", node("lvalue"), ", (", "FIXME", "), ", node("record"), ", (", name("record_type"), "))")
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
        hasBase(ignoringParenImpCasts(memberExpr(member(has(typeLoc().bind("record_type")))).bind("record")))
      ).bind("lvalue"),
      {
        changeTo(
          before(node("lvalue")),
          cat("__trace_member_lvalue(")
        ),
        changeTo(
          after(node("lvalue")),
          cat(", ", node("lvalue"), ", (", "FIXME", "), ", node("record"), ", (", name("record_type"), "))")
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
        hasDescendant(expr()), // 代入を伴うこと
        hasParent(declStmt( // 文法破壊防止
          unless(hasParent(forStmt())),
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
  auto HandleLvalueDeclRefExpr = makeRule(
      declRefExpr(
        unless(isInMacro()),
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_lvalue,
        // unless(hasAncestor(varDecl())),
        unless(hasAncestor(memberExpr())),
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
  auto HandleLvalueMemberExpr = makeRule(
      memberExpr(
        unless(isInMacro()),
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_lvalue,
        is_not_in_initlistexpr,
        is_not_increment,
        unless(is_bitfield), // TODO: bit field はトレース対象外なのはなんとかしたいな
        is_not_pointer_operation,
        unless(hasAncestor(memberExpr())),
        member(fieldDecl(hasTypeLoc(typeLoc().bind("lvalue_type")))),
        capture_record_type
      ).bind("lvalue"),
      {
        // NOTE: メンバー参照が連続する場合（v.a->b）はノードを含めて書き換えた方が楽
        insertBefore(
          node("lvalue"),
          cat("__trace_member_lvalue(")
        ),
        insertAfter(
          node("lvalue"),
          cat(", ", node("lvalue"), ", (", node("lvalue_type"), "), ", node("record"), ", (", name("record_type"), "))")
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
        anyOf(
          // 一時変数
          to(varDecl(unless(isRegister()), hasTypeLoc(typeLoc().bind("rvalue_type")))),
          // 関数引数
          to(parmVarDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
          // 関数定義
          to(functionDecl(hasTypeLoc(typeLoc().bind("rvalue_type"))))
        )
      ).bind("rvalue"),
      {
        insertBefore(
          node("rvalue"), 
          cat("__trace_variable_rvalue(")
        ),
        insertAfter(
          node("rvalue"), 
          cat(", ", node("rvalue"), ", (", name("rvalue_type"), "))")
        ),
        add_include,
      },
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
  // FIXME: マイナス値が -(____trace_variable_rvalue(1, const int)) になってしまう。
  auto change_rvalue_const_int = {
      insertBefore(
        node("rvalue"), 
        cat("__trace_variable_rvalue(")
      ),
      insertAfter(
        node("rvalue"), 
        cat(", ", node("rvalue"), ", (", "const int", "))")
      ),
      add_include,
    };
  auto HandleRvalueIntegerLiteral = makeRule(
      // TODO: v += u を v = v + u に正規化
      integerLiteral(
        isExpansionInMainFile(),
        unless(isExpansionInSystemHeader()),
        is_not_in_case,
        is_not_in_initlistexpr,
        is_not_in_static_vardecl,
        is_not_in_global_vardecl,
        is_not_in_array_vardecl,
        is_not_in_fielddecl,
        is_not_in_enum,
        unless(hasAncestor(varDecl(hasAlignedAttr())))
      ).bind("rvalue"),
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
      {
        insertBefore(
          node("rvalue"), 
          cat("__trace_variable_rvalue(")
        ),
        insertAfter(
          node("rvalue"), 
          cat(", ", node("rvalue"), ", (", node("rvalue_type"), "))")
        ),
        add_include,
      },
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
  auto HandleRvalueMemberExpr = makeRule(
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
        member(fieldDecl(hasTypeLoc(typeLoc().bind("rvalue_type")))),
        capture_record_type
      ).bind("rvalue"),
      {
        // NOTE: メンバー参照が連続する場合（v.a->b）はノードを含めて書き換えた方が楽
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
      assignment_found("HandleRvalueMemberExpr")
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

    HandleRvalueNull,
    HandleRvalueSizeofExpr,
    HandleRvalueReferenceExpr,
    HandleRvalueMemberExprArraySubscriptExpr,
    HandleRvalueArraySubscriptExpr,
    HandleRvalueMemberExpr,
    HandleRvalueDeclRefExpr,
    HandleRvalueIntegerLiteral,
    HandleRvalueStringLiteral,

    HandleLvalueMemberExprArraySubscriptExpr,
    HandleLvalueArraySubscriptExpr,
    HandleLvalueMemberExpr,
    HandleLvalueDeclRefExpr,
  });
}

VariableUpdateTracingCheck::VariableUpdateTracingCheck(StringRef Name,
                                               ClangTidyContext *Context)
    : utils::TransformerClangTidyCheck(VariableUpdateTracingCheckImpl(), Name, Context) {}

} // namespace misc
} // namespace tidy
} // namespace clang
