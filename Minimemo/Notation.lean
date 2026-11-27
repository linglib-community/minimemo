/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Syntax
public meta import Lean.Elab.Term

/-!
# Notation for memo models

This file lets a memo model be written in Lean in the syntax of memo.

The term `memo% [u : U, r : R] s₁ s₂ … return e` is the model with the axes `u` and `r`, the
statements `sᵢ` and the returned expression `e`. Names of agents, choices, domains and outside
functions are written as in memo and stand for the constructors of the types of names with those
names.

## Main definitions

* `memo% …`: a model in the syntax of memo.

## Implementation notes

The words `chooses`, `thinks`, `observes`, `knows`, `wpp`, `is`, `Pr` and `E` are not reserved, so
they remain available as identifiers outside a model.
-/

@[expose] public section

namespace Memo

/-- An expression of memo. -/
declare_syntax_cat memo_expr
/-- A statement of memo. -/
declare_syntax_cat memo_stmt

syntax num : memo_expr
syntax ident : memo_expr
syntax ident "(" memo_expr,* ")" : memo_expr
syntax ident "[" memo_expr "]" : memo_expr
syntax "(" memo_expr ")" : memo_expr
syntax:50 memo_expr:51 " == " memo_expr:51 : memo_expr
syntax:65 memo_expr:65 " + " memo_expr:66 : memo_expr
syntax:65 memo_expr:65 " - " memo_expr:66 : memo_expr
syntax:70 memo_expr:70 " * " memo_expr:71 : memo_expr
syntax:70 memo_expr:70 " / " memo_expr:71 : memo_expr

syntax ident ":" &"chooses" "(" ident " in " ident "," &"wpp" "=" memo_expr ")" : memo_stmt
syntax ident ":" &"thinks" "[" memo_stmt,+ "]" : memo_stmt
syntax ident ":" &"observes" "[" ident "]" &"is" ident : memo_stmt
syntax ident ":" &"knows" "(" ident ")" : memo_stmt

/-- An axis of a model: a name and a domain. -/
syntax memoAxis := ident ":" ident

/-- A model in the syntax of memo. -/
syntax (name := memoModel) "memo% " "[" memoAxis,* "]" memo_stmt* "return " memo_expr : term

end Memo

end

namespace Memo.Notation

open Lean

/-- The constructor with the name `n`, written `.n`. -/
meta def dot (n : Name) : Term :=
  ⟨Syntax.node .none ``Lean.Parser.Term.dotIdent #[mkAtom ".", mkIdent n]⟩

/-- An agent and a choice from a name such as `speaker.x`, or a choice of the current agent. -/
meta def address (n : Name) : Option Name × Name :=
  match n with
  | .str (.str .anonymous a) x => (some (.mkSimple a), .mkSimple x)
  | n => (none, n)

meta partial def expr : TSyntax `memo_expr → MacroM Term
  | `(memo_expr| $n:num) => `(Memo.Expr.lit $n)
  | `(memo_expr| ($e)) => expr e
  | `(memo_expr| $a == $b) => do `(Memo.Expr.prim Memo.Prim.eq ![$(← expr a), $(← expr b)])
  | `(memo_expr| $a + $b) => do `(Memo.Expr.prim Memo.Prim.add ![$(← expr a), $(← expr b)])
  | `(memo_expr| $a - $b) => do `(Memo.Expr.prim Memo.Prim.sub ![$(← expr a), $(← expr b)])
  | `(memo_expr| $a * $b) => do `(Memo.Expr.prim Memo.Prim.mul ![$(← expr a), $(← expr b)])
  | `(memo_expr| $a / $b) => do `(Memo.Expr.prim Memo.Prim.div ![$(← expr a), $(← expr b)])
  | `(memo_expr| $f:ident ( $args,* )) => do
    let args ← args.getElems.mapM expr
    `(Memo.Expr.call $(dot f.getId) ![$args,*])
  | `(memo_expr| $f:ident [ $e ]) => do
    let e ← expr e
    if f.getId == `Pr || f.getId == `E then `(Memo.Expr.expect $e)
    else `(Memo.Expr.query $(dot f.getId) $e)
  | `(memo_expr| $x:ident) =>
    match address x.getId with
    | (some a, x) => `(Memo.Expr.query $(dot a) (Memo.Expr.choice $(dot x)))
    | (none, x) => `(Memo.Expr.choice $(dot x))
  | _ => Macro.throwUnsupported

meta def ref (a : Option Name) : MacroM Term :=
  match a with
  | some a => `(Memo.Ref.agent $(dot a))
  | none => `(Memo.Ref.self)

meta partial def stmt : TSyntax `memo_stmt → MacroM Term
  | `(memo_stmt| $a:ident : chooses ( $x:ident in $d:ident , wpp = $e )) => do
    `(Memo.Stmt.chooses $(dot a.getId) $(dot x.getId) $(dot d.getId) $(← expr e))
  | `(memo_stmt| $a:ident : thinks [ $ss,* ]) => do
    `(Memo.Stmt.thinks $(dot a.getId) $(← seq (← ss.getElems.mapM stmt)))
  | `(memo_stmt| $a:ident : observes [ $t:ident ] is $s:ident) => do
    let (some b, x) := address t.getId | Macro.throwError "the choice of another agent is expected"
    let (g, y) := address s.getId
    `(Memo.Stmt.observes $(dot a.getId) $(dot b) $(dot x) $(← ref g) $(dot y))
  | `(memo_stmt| $a:ident : knows ( $s:ident )) => do
    let (g, y) := address s.getId
    `(Memo.Stmt.knows $(dot a.getId) $(← ref g) $(dot y))
  | _ => Macro.throwUnsupported
where
  /-- Statements in sequence. -/
  seq (ss : Array Term) : MacroM Term := do
    if h : 0 < ss.size then
      let last := ss[ss.size - 1]
      ss.pop.foldrM (fun s t ↦ `(Memo.Stmt.seq $s $t)) last
    else `(Memo.Stmt.pass)

@[macro Memo.memoModel] public meta def model : Macro
  | `(memo% [ $axes,* ] $ss* return $e) => do
    let axes ← axes.getElems.mapM fun
      | `(Memo.memoAxis| $x:ident : $d:ident) => `(($(dot x.getId), $(dot d.getId)))
      | _ => Macro.throwUnsupported
    `(({ axes := [$axes,*], body := $(← stmt.seq (← ss.mapM stmt)), ret := $(← expr e) } :
      Memo.Model _ _ _ _))
  | _ => Macro.throwUnsupported

end Memo.Notation
