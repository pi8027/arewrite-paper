From elpi Require Import elpi.
From mathcomp Require Import ssrmatching ssreflect ssrfun ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope monoid_scope.
Local Open Scope monoid_scope.

(* Multiplicative monoids *)
Module MulMonoid.

Structure type := {
  sort : Type;
  one : sort;
  mul : sort -> sort -> sort;
  mulA : forall x y z, mul x (mul y z) = mul (mul x y) z;
  mul1x : forall x, mul one x = x;
  mulx1 : forall x, mul x one = x;
}.

End MulMonoid.

Notation monoidType := MulMonoid.type.
#[reversible]
Coercion MulMonoid.sort : monoidType >-> Sortclass.

Arguments MulMonoid.one {M} : rename.
Arguments MulMonoid.mul {M} : rename.
Notation one := MulMonoid.one.
Notation mul := MulMonoid.mul.
Notation mulA := MulMonoid.mulA.
Notation mul1x := MulMonoid.mul1x.
Notation mulx1 := MulMonoid.mulx1.
Notation "1" := one : monoid_scope.
Notation "x * y" := (mul x y) : monoid_scope.

Implicit Type M : monoidType.

Canonical list_monoidType (T : Type) :=
  {| MulMonoid.sort := list T;
     MulMonoid.one := nil;
     MulMonoid.mul := cat;
     MulMonoid.mulA := @catA _;
     MulMonoid.mul1x := @cat0s _;
     MulMonoid.mulx1 := @cats0 _; |}.

(* Structure of invertible elements *)
Module Invertible.
Structure type M : Type := { sort : M; inv : M; }.
End Invertible.

Notation invertible := Invertible.type.
#[reversible]
Coercion Invertible.sort : invertible >-> MulMonoid.sort.

Arguments Invertible.inv {M}.
Notation inv := Invertible.inv.

Module LInvertible.

Structure type M : Type := { sort : M; inv : M; mulVx : inv * sort = 1; }.

Definition invertible M (x : type M) :=
  {| Invertible.sort := sort x; Invertible.inv := inv x |}.

End LInvertible.

Notation lInvertible := LInvertible.type.
#[reversible]
Coercion LInvertible.sort : lInvertible >-> MulMonoid.sort.
Coercion LInvertible.invertible : lInvertible >-> invertible.
Canonical LInvertible.invertible.

Lemma mulVx {M} (x : lInvertible M) : inv x * x = 1.
Proof. by case: x. Qed.

Module RInvertible.

Structure type M : Type := { sort : M; inv : M; mulxV : sort * inv = 1; }.

Definition invertible M (x : type M) :=
  {| Invertible.sort := sort x; Invertible.inv := inv x |}.

End RInvertible.

Notation rInvertible := RInvertible.type.
#[reversible]
Coercion RInvertible.sort : rInvertible >-> MulMonoid.sort.
Coercion RInvertible.invertible : rInvertible >-> invertible.
Canonical RInvertible.invertible.

Lemma mulxV {M} (x : rInvertible M) : x * inv x = 1.
Proof. by case: x. Qed.

Module LRInvertible.

Structure type M : Type :=
  { sort : M; inv : M; mulVx : inv * sort = 1; mulxV : sort * inv = 1; }.

Definition invertible M (x : type M) :=
  {| Invertible.sort := sort x; Invertible.inv := inv x |}.
Definition lInvertible M (x : type M) :=
  {| LInvertible.sort := sort x; LInvertible.mulVx := mulVx x |}.
Definition rInvertible M (x : type M) :=
  {| RInvertible.sort := sort x; RInvertible.mulxV := mulxV x |}.

End LRInvertible.

Notation lrInvertible := LRInvertible.type.
#[reversible]
Coercion LRInvertible.sort : lrInvertible >-> MulMonoid.sort.
Coercion LRInvertible.invertible : lrInvertible >-> invertible.
Coercion LRInvertible.lInvertible : lrInvertible >-> lInvertible.
Coercion LRInvertible.rInvertible : lrInvertible >-> rInvertible.
Canonical LRInvertible.invertible.
Canonical LRInvertible.lInvertible.
Canonical LRInvertible.rInvertible.

(* left (resp. right) inverse is canonically right (resp. left) invertible *)

Canonical inv_invertible M (x : invertible M) :=
  {| Invertible.sort := inv x; Invertible.inv := x |}.
Canonical inv_rInvertible M (x : lInvertible M) :=
  {| RInvertible.sort := inv x; RInvertible.mulxV := mulVx x |}.
Canonical inv_lInvertible M (x : rInvertible M) :=
  {| LInvertible.sort := inv x; LInvertible.mulVx := mulxV x |}.
Canonical inv_lrInvertible M (x : lrInvertible M) :=
  {| LRInvertible.sort := inv x;
     LRInvertible.mulxV := mulVx x; LRInvertible.mulVx := mulxV x |}.

(* The infrastructure for proof by reflection *)
Module Import Internals.

(* syntax trees for reasoning modulo associativity *)
Inductive aexpr M : Type :=
  | ae_mul : aexpr M -> aexpr M -> aexpr M
  | ae_one : aexpr M
  | ae_var : M -> aexpr M.

Definition ae_cons {M} (x : M) : aexpr M -> aexpr M := ae_mul (ae_var x).

Fixpoint ae_eval {M} (e : aexpr M) : M :=
  match e with
  | ae_mul e1 e2 => ae_eval e1 * ae_eval e2
  | ae_one => 1
  | ae_var x => x
  end.

Fixpoint ae_norm {M} (e : aexpr M) (acc : M) : M :=
  match e with
  | ae_mul e1 e2 => ae_norm e1 (ae_norm e2 acc)
  | ae_one => acc
  | ae_var x => x * acc
  end.

(* syntax trees for reasoning modulo cancellation (of left and right inverse) *)
Inductive iexpr M : Type :=
  can_inv : rInvertible M -> list (iexpr M) -> iexpr M.

Fixpoint ie_eval {M} (e : iexpr M) (acc : M) : M :=
  let: can_inv x es := e in x * foldr ie_eval (inv x * acc) es.

Inductive cexpr M : Type :=
  | ce_cons : M -> cexpr M -> cexpr M
  | ce_one : cexpr M
  | ce_icons (f : bool) : iexpr M -> cexpr M -> cexpr M.

Fixpoint ce_eval {M} (f : bool) (e : cexpr M) (acc : M) : M :=
  match e with
  | ce_cons m e => m * ce_eval f e acc
  | ce_one => acc
  | ce_icons f' e1 e2 =>
    (if eqb f f' then ie_eval e1 else id) (ce_eval f e2 acc)
  end.

Lemma ae_correct {M} (e : aexpr M) (acc : M) : ae_eval e * acc = ae_norm e acc.
Proof.
elim: e acc => //=; last by move=> acc; rewrite mul1x.
by move=> e1 IHe1 e2 IHe2 acc; rewrite -mulA IHe2 IHe1.
Qed.

Lemma ie_correct {M} (e : iexpr M) (acc : M) : ie_eval e acc = acc.
Proof.
move: e acc; fix IHe 1 => -[] x /=; elim => [|e es IHes] acc /=.
  by rewrite mulA mulxV mul1x.
by rewrite IHe IHes.
Qed.

Lemma ce_correct {M} (e : cexpr M) (acc : M) :
  ce_eval false e acc = ce_eval true e acc.
Proof.
elim: e acc => //= [x e IHe|f e1 e2 IHe2] acc; first by rewrite IHe.
by case: f; rewrite /= ie_correct.
Qed.

(* lemmas for areflexivity *)
Lemma areflexivity_correct {M} (e1 e2 : aexpr M) :
  ae_norm e1 1 = ae_norm e2 1 -> ae_eval e1 = ae_eval e2.
Proof. by rewrite -!ae_correct !mulx1. Qed.

(* lemmas for arewrite *)
Lemma add_prepost {M} (pre x y post : M) :
  x = y -> (pre * x) * post = (pre * y) * post.
Proof. by move=> ->. Qed.

Lemma arewrite_correct {M} (e lhs : aexpr M) (rhs : M) :
  ae_norm e 1 = ae_norm lhs 1 -> ae_eval lhs = rhs -> ae_eval e = rhs.
Proof. by rewrite -!ae_correct !mulx1 => ->. Qed.

(* lemmas for aireflexivity *)
Lemma aireflexivity_correct {M} (e1 e2 : aexpr M) (ce : cexpr M) :
  ae_norm e1 1 = ce_eval false ce 1 -> ce_eval true ce 1 = ae_norm e2 1 ->
  ae_eval e1 = ae_eval e2.
Proof. by rewrite -!ae_correct ce_correct !mulx1 => ->. Qed.

(* lemmas for airewrite *)
Lemma airewrite_correct {M} (e lhs : aexpr M) (rhs : M) (ce : cexpr M) :
  ae_norm e 1 = ce_eval false ce 1 -> ce_eval true ce 1 = ae_norm lhs 1 ->
  ae_eval lhs = rhs -> ae_eval e = rhs.
Proof. by rewrite -!ae_correct ce_correct !mulx1 => -> ->. Qed.

End Internals.

(* Elpi code for areflexivity *)

Elpi Tactic areflexivity.
Elpi Accumulate lp:{{

% [quote M In Out] takes an element [In] of monoid [M], and reifies it to [Out].
% pred quote i:term i:term o:term.
func quote term, term -> term.
quote M {{ @one lp:M' }} {{ @ae_one lp:M }} :- coq.unify-eq M M' ok, !.
quote M {{ @mul lp:M' lp:In1 lp:In2 }} {{ @ae_mul lp:M lp:Out1 lp:Out2 }} :-
  coq.unify-eq M M' ok, !, quote M In1 Out1, quote M In2 Out2.
quote M In {{ @ae_var lp:M lp:In }} :- !.

solve (goal _ _ Type _ _ as G) [] :- @ltacfail! 0 => std.do! [
  std.assert-ok!
    (coq.unify-eq Type {{ @eq (MulMonoid.sort lp:M) lp:LHS lp:RHS }})
    "The goal is not a monoid equation",
  quote M LHS LHSQ,
  quote M RHS RHSQ,
  (refine {{ @areflexivity_correct lp:M lp:LHSQ lp:RHSQ erefl }} G [];
   coq.ltac.fail 0 "Not a valid equivalence")
].

}}.

(* Common Elpi code for arewrite, aireflexivity, and airewrite *)

Elpi File common.elpi lp:{{

func app-dir string, term -> term.
app-dir "lr" Proof Proof :- !.
app-dir "rl" Proof {{ @esym _ _ _ lp:Proof }} :- !.

% a list-like representation of "paths", produced by [quote] below
kind path type.
% [nilp] is the empty path (= identity)
type nilp path.
% [consp X P] is the cons cell (multiplication) of an element [X] and a path [P]
type consp term -> path -> path.
% [catp P Q] is the concatenation (multiplication) of two paths [P] and [Q].
% Unlike [consp], [catp] is used for representing open terms, and [P] must be an
% evar.
type catp path -> path -> path.

% [path.split P Pl Pr] splits a path [P] (with no unification variable) into
% [Pl] and [Pr]. This predicate enumerates all such solutions.
pred path.split i:path, o:path, o:path.
path.split P nilp P.
path.split (consp X P) (consp X Pl) Pr :- path.split P Pl Pr.

% [quote M In Out OutP] takes an element [In] of monoid [M], reifies it to [Out]
% and flattens it to a path [OutP].
func quote term, term -> term, path.
quote M In Out (OutP nilp) :- !, quote-rec M In Out OutP.

func quote-rec term, term -> term, (path -> path).
quote-rec M In Out (catp OutP) :-
  % when the input is a unification variable, suspend the reification process.
  % It will later be resumed by [path.quote] when [OutP] get instantiated.
  var In, !, declare_constraint (path.quote M OutP In Out) OutP.
quote-rec M {{ @one lp:M' }} {{ @ae_one lp:M }} (p\ p) :-
  coq.unify-eq M M' ok, !.
quote-rec M {{ @mul lp:M' lp:In1 lp:In2 }}
    {{ @ae_mul lp:M lp:Out1 lp:Out2 }} (p\ OutP1 (OutP2 p)) :-
  coq.unify-eq M M' ok, !,
  quote-rec M In1 Out1 OutP1, quote-rec M In2 Out2 OutP2.
quote-rec M In {{ @ae_var lp:M lp:In }} (consp In).

func path.quote term, path -> term, term.
path.quote M P Out OutQ :-
  var P, !, declare_constraint (path.quote M P Out OutQ) P.
path.quote M nilp {{ @one lp:M }} {{ @ae_one lp:M }} :- !.
path.quote M (consp _ P' as P) Out OutQ :-
  var P', !, declare_constraint (path.quote M P Out OutQ) P'.
path.quote M (consp X nilp) X {{ @ae_var lp:M lp:X }} :- !.
path.quote M (consp X P)
    {{ @mul lp:M lp:X lp:Out }} {{ @ae_cons lp:M lp:X lp:OutQ }} :-
  path.quote M P Out OutQ.

}}.

(* Elpi code for arewrite *)

Elpi Tactic arewrite_proofgen.
Elpi Accumulate File common.elpi.
Elpi Accumulate lp:{{

% [path.match P Q] unifies two paths [P] and [Q]. [P] corresponds to the
% selected subterm and must be a ground term. [Q] corresponds to the LHS and may
% contain unification variables.
pred path.match i:path, o:path.
path.match nilp nilp :- !.
path.match (consp X P) (consp X' P') :- !,
  coq.unify-eq X X' ok, path.match P P'.
path.match P (catp Pl Pr') :-
  path.split P Pl Pr, % resume [path.quote] here
  path.match Pr Pr'.

solve (goal _ _ _ _ [str Dir, trm Scr, trm Proof] as G) GS :-
  @ltacfail! 0 => std.do! [
    std.assert-ok! (coq.typecheck Scr {{ MulMonoid.sort lp:M }})
      "The type of the given subterm is not a monoid",
    std.assert-ok! (coq.elaborate-skeleton Proof ProofTy Proof')
      "The given proof does not typecheck",
    app-dir Dir { coq.saturate ProofTy Proof' } Proof'',
    Proof''' = {{ @add_prepost _ _ _ _ _ lp:Proof'' }},
    std.assert-ok!
      (coq.typecheck Proof''' {{ @eq (MulMonoid.sort lp:M) lp:LHS lp:RHS }})
      "The given proof is not a monoid equality",
    path.match {quote M Scr ScrQ} {quote M LHS LHSQ},
    std.assert-ok! (coq.typecheck ScrQ _) "ScrQ does not type-check",
    std.assert-ok! (coq.typecheck LHSQ _) "LHSQ does not type-check",
    (refine {{ @arewrite_correct lp:M lp:ScrQ lp:LHSQ lp:RHS
                 erefl lp:Proof''' }} G GS;
     coq.ltac.fail 0 "arewrite_proofgen failed")
  ].

}}.

(* Common Elpi code for aireflexivity and airewrite *)

Elpi File inv_common.elpi lp:{{

% [path.cat P Q PQ] concatenates two paths [P] and [Q] into [PQ].
func path.cat path, path -> path.
path.cat nilp P P :- !.
path.cat (consp M P) Q (consp M PQ) :- !, path.cat P Q PQ.
path.cat (catp Pl Pr) Q (catp Pl PrQ) :- !, path.cat Pr Q PrQ.

% [rinv->linv M X Ri Y] takes a right-invertible element [X] in monoid [M], and
% returns its right-invertible instance [Ri] and the inverse [Y].
func rinv->linv term, term -> term, term.
rinv->linv M X {{ @inv_rInvertible lp:M lp:Li }}
               {{ @LInvertible.sort lp:M lp:Li }} :-
  coq.unify-eq X {{ @inv lp:M (@LInvertible.invertible lp:M lp:Li) }} ok, !.
rinv->linv M X Ri {{ @inv lp:M (@RInvertible.invertible lp:M lp:Ri) }} :-
  coq.unify-eq X {{ @RInvertible.sort lp:M lp:Ri }} ok, !.

% [linv->rinv M X Ri Y] takes a left-invertible element [X] in monoid [M], and
% returns its inverse [Y] and the right-invertible instance [Ri] on it.
func linv->rinv term, term -> term, term.
linv->rinv M X Ri {{ @RInvertible.sort lp:M lp:Ri }} :-
  coq.unify-eq X {{ @inv lp:M (@RInvertible.invertible lp:M lp:Ri) }} ok, !.
linv->rinv M X {{ @inv_rInvertible lp:Li }}
               {{ @inv lp:M (@LInvertible.invertible lp:M lp:Li) }} :-
  coq.unify-eq X {{ @LInvertible.sort lp:M lp:Li }} ok, !.

% [mkrocqlist T In Out] takes an (Elpi) list [In] of terms of type [T], and
% turns it into a (Rocq) list [Out] of type [list T].
func mkrocqlist term, list term -> term.
mkrocqlist T In Out :-
  std.fold-right In {{ @nil lp:T }}
    (o\ t\ t'\ t' = {{ @cons lp:T lp:o lp:t }}) Out.

% [iexprs->cexpr M B IES Acc Out] takes
% - [B]: a term of type [bool],
% - [IES]: an (Elpi) list of terms of type [iexpr M], and
% - [Acc]: a term of type [cexpr M],
% and returns a term [Out] of type [iexpr M], prepending [IES] to [Acc] using
% the [@ce_icons M B] constructor.
func iexprs->cexpr term, term, list term, term -> term.
iexprs->cexpr M B IES Acc Out :-
  std.fold-right IES Acc
    (o\ t\ t'\ t' = {{ @ce_icons lp:M lp:B lp:o lp:t }}) Out.

}}.

(* Elpi code for aireflexivity *)

Elpi Tactic aireflexivity.
Elpi Accumulate File common.elpi.
Elpi Accumulate File inv_common.elpi.
Elpi Accumulate lp:{{

% [skip-one M P Q Out] takes a path [P] in monoid [M], and splits it into:
% - the shortest nonempty prefix that is [one] modulo cancellation, represented
%   as the reified term [Out] of type [iexpr M], and
% - the rest of the path (suffix) [Q].
func skip-one term, path -> path, term.
skip-one M (consp X P) P'' {{ @can_inv lp:M lp:Ri lp:Out }} :- !,
  % Check if [X] is right invertible
  rinv->linv M X Ri XV, !,
  % [skip-ones] below may return several solutions (from short to long)
  skip-ones M P (consp XV' P'') OutL,
  coq.unify-eq XV XV' ok,
  % commit to the first (thus shortest) solution
  !,
  % turning the list [OutL] in Elpi into a list [Out] in Rocq
  mkrocqlist {{ @iexpr lp:M }} OutL Out.

% [skip-ones M P Q Out] takes a path [P] in monoid [M], and splits it into:
% - a prefix that is [one] modulo cancellation, represented as a list [Out] of
%   reified terms of type [iexpr M], and
% - the rest of the path (suffix) [Q].
% [skip-ones] is non-deterministic, i.e., may have several solutions. It
% enumerates from shorter to longer solutions.
pred skip-ones i:term, i:path, o:path, o:list term.
skip-ones _ P P [].
skip-ones M P P2 [Out1|Out2] :- skip-one M P P1 Out1, !, skip-ones M P1 P2 Out2.

% [path.match(') M P Q Out] unifies two paths [P] and [Q] in monoid [M] modulo
% cancellation, and produces a witness [Out] of type [cexpr M] that [P] and [Q]
% are equal modulo cancellation.
% [P] corresponds to the selected subterm and must be a ground term.
% [Q] corresponds to the LHS and may contain unification variables.
% [path.match] and [path.match'] are mutually recursive. The former first skips
% the prefixes of [P] and [Q] that are [one] modulo cancellation, while the
% latter does not.
pred path.match i:term, i:path, i:path, o:term.
path.match M P Q Out'' :-
  % again, [skip-ones] below may return several solutions (from short to long)
  skip-ones M P P' OutP,
  skip-ones M Q Q' OutQ,
  path.match' M P' Q' Out,
  iexprs->cexpr M {{ false }} OutP Out Out',
  iexprs->cexpr M {{ true }} OutQ Out' Out''.

pred path.match' i:term, i:path, i:path, o:term.
path.match' M nilp nilp {{ @ce_one lp:M }} :- !.
path.match' M (consp X P) (consp X' Q) {{ @ce_cons lp:M lp:X lp:Out }} :- !,
  coq.unify-eq X X' ok, path.match M P Q Out.

solve (goal _ _ Type _ _ as G) GS :- @ltacfail! 0 => std.do! [
  std.assert-ok!
    (coq.unify-eq Type {{ @eq (MulMonoid.sort lp:M) lp:LHS lp:RHS }})
    "The goal is not a monoid equation",
  quote M LHS LHSQ LHSP,
  quote M RHS RHSQ RHSP,
  path.match M LHSP RHSP CE,
  (refine {{ @aireflexivity_correct lp:M lp:LHSQ lp:RHSQ lp:CE erefl erefl }}
     G GS;
   coq.ltac.fail 0 "Not a valid equivalence")
].

}}.

(* Elpi code for airewrite *)

Elpi Tactic airewrite_proofgen.
Elpi Accumulate File common.elpi.
Elpi Accumulate File inv_common.elpi.
Elpi Accumulate lp:{{

% [path->cexpr M P Acc Out] prepends a path [P] in monoid [M] with [Acc] of type
% [cexpr M], returns [Out] of type [cexpr M].
func path->cexpr term, path, term -> term.
path->cexpr _ nilp Acc Acc :- !.
path->cexpr M (consp X P) Acc {{ @ce_cons lp:M lp:X lp:Out }} :- !,
  path->cexpr M P Acc Out.

% [skip-one M P Q Out] takes a path [P] in monoid [M], and splits it into:
% - the shortest nonempty prefix that is [one] modulo cancellation, represented
%   as the reified term [Out] of type [iexpr M], and
% - the rest of the path (suffix) [Q].
%
% FIXME: [skip-one] should probably be considered deterministic, but Elpi cannot
% treat it as a function because [P] is an output parameter?
pred skip-one i:term, o:path, o:path, o:term.
skip-one M (consp X P) P'' {{ @can_inv lp:M lp:Ri lp:Out }} :- !,
  % Check if [X] is right invertible
  rinv->linv M X Ri XV, !,
  % [skip-ones] below may return several solutions (from short to long)
  skip-ones M P P' OutL,
  % if [P'] is [consp], check if its head is [XV]
  ((P' = consp XV' P'', !, coq.unify-eq XV XV' ok);
  % if [P'] is [catp], instantiate its head with [XV] and partially resume
  % [path.quote]
   (P' = catp (consp XV Pl) Pr, !, P'' = catp Pl Pr)),
  % commit to the first (thus shortest) solution
  !,
  % turning the list [OutL] in Elpi into a list [Out] in Rocq
  mkrocqlist {{ @iexpr lp:M }} OutL Out.

% [skip-ones M P Q Out] takes a path [P] in monoid [M], and splits it into:
% - a prefix that is [one] modulo cancellation, represented as a list [Out] of
%   reified terms of type [iexpr M], and
% - the rest of the path (suffix) [Q].
% [skip-ones] is non-deterministic, i.e., may have several solutions. It
% enumerates from shorter to longer solutions.
pred skip-ones i:term, o:path, o:path, o:list term.
skip-ones _ P P [].
skip-ones M P P2 [Out1|Out2] :- skip-one M P P1 Out1, !, skip-ones M P1 P2 Out2.

% [skip-one_catp M P Acc Q PV Acc'] takes a path [P] in monoid [M], recognizes
% a prefix of the form:
%   (one modulo cancellation)^*
%   f1 (which is left invertible)
%   ...
%   (one modulo cancellation)^*
%   fn (which is left invertible)
% and returns
%   [Q]: the rest of the path
%   [PV]: the path fn^-1, ..., f1^-1, and
%   [Acc']: the list of witnesses of type [iexpr M] that the composition of [PV]
%           and the prefix is one modulo cancellation
pred skip-one_catp i:term, i:path, i:list term, o:path, o:path, o:list term.
skip-one_catp _ P Acc P nilp Acc.
skip-one_catp M P Acc Q (consp EV PV) Acc''' :-
  skip-ones M P (consp E P') Acc',
  linv->rinv M E Ri EV,
  mkrocqlist {{ @iexpr lp:M }} {std.append Acc Acc'} Acc'',
  skip-one_catp M P' [{{ @can_inv lp:M lp:Ri lp:Acc'' }}] Q PV Acc'''.

% [path.match(') M P Q Out] unifies two paths [P] and [Q] in monoid [M] modulo
% cancellation, and produces a witness [Out] of type [cexpr M] that [P] and [Q]
% are equal modulo cancellation.
% [P] corresponds to the selected subterm and must be a ground term.
% [Q] corresponds to the LHS and may contain unification variables.
% [path.match] and [path.match'] are mutually recursive. The former first skips
% the prefixes of [P] and [Q] that are [one] modulo cancellation, while the
% latter does not.
pred path.match i:term, i:path, o:path, o:term.
path.match M P Q Out'' :-
  % again, [skip-ones] below may return several solutions (from short to long)
  skip-ones M P P' OutP,
  skip-ones M Q Q' OutQ,
  path.match' M P' Q' Out,
  iexprs->cexpr M {{ false }} OutP Out Out',
  iexprs->cexpr M {{ true }} OutQ Out' Out''.

pred path.match' i:term, i:path, o:path, o:term.
path.match' M nilp nilp {{ @ce_one lp:M }} :- !.
path.match' M (consp X P) (consp X' Q) {{ @ce_cons lp:M lp:X lp:Out }} :- !,
  coq.unify-eq X X' ok, path.match M P Q Out.
path.match' M P (catp QVar Q) Out'' :-
  skip-one_catp M Q [] Qr QlV QlW,
  path.split P Pl Pr,
  path.cat Pl QlV QVar, % resume [path.quote] here
  path.match M Pr Qr Out,
  iexprs->cexpr M {{ true }} QlW Out Out',
  path->cexpr M Pl Out' Out''.

solve (goal _ _ _ _ [str Dir, trm Scr, trm Proof] as G) GS :-
  @ltacfail! 0 => std.do! [
    std.assert-ok! (coq.typecheck Scr {{ MulMonoid.sort lp:M }})
      "The type of the given subterm is not a monoid",
    std.assert-ok! (coq.elaborate-skeleton Proof ProofTy Proof')
      "The given proof does not typecheck",
    app-dir Dir { coq.saturate ProofTy Proof' } Proof'',
    Proof''' = {{ @add_prepost _ _ _ _ _ lp:Proof'' }},
    std.assert-ok!
      (coq.typecheck Proof''' {{ @eq (MulMonoid.sort lp:M) lp:LHS lp:RHS }})
      "The given proof is not a monoid equality",
    path.match M {quote M Scr ScrQ} {quote M LHS LHSQ} CE,
    % std.assert-ok! (coq.typecheck ScrQ _) "ScrQ does not type-check",
    % std.assert-ok! (coq.typecheck LHSQ _) "LHSQ does not type-check",
    % std.assert-ok! (coq.typecheck CE _) "CE does not type-check",
    (refine {{ @airewrite_correct lp:M
                 lp:ScrQ lp:LHSQ lp:RHS lp:CE erefl erefl lp:Proof''' }} G GS;
     coq.ltac.fail 0 "arewrite_proofgen failed")
  ].

}}.

(*********************)
(* Exporting tactics *)
(*********************)

Ltac areflexivity := elpi areflexivity.
Ltac aireflexivity := elpi aireflexivity.

(* The syntax of the rewriting tactics is similar to Ssreflect rewrite.       *)
(* - It starts with the tactic name: either `arewrite` or `airewrite`.        *)
(* - It is optionally followed by `-` that indicates rewriting from right to  *)
(*   left. The default is left to right.                                      *)
(* - It is optionally followed by `[pattern]` for selecting the subterm to    *)
(*   rewrite. See the following paper for the details:                        *)
(*     G. Gonthier, E. Tassi. A language of patterns for subterm selection.   *)
(*     In: Proc. of ITP '12, 2012.                                            *)
(* - It ends with the proof term of the equation for rewriting.               *)
(* Example: `airewrite -[a]H` rewrites a subterm in the goal of form `a` with *)
(* the given equational proof `H`, from right to left.                        *)
(* NB: We do not support chaining several rewriting steps in one tactic call  *)
(* for now, since it seems impossible to implement without writing an OCaml   *)
(* plugin.                                                                    *)

(* arewrite *)

Tactic Notation "arewrite" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi arewrite_proofgen "lr" (Selected) (proof));
    rewrite 1?mul1x 1?mulx1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "arewrite" "-" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi arewrite_proofgen "rl" (Selected) (proof));
    rewrite 1?mul1x 1?mulx1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "arewrite" uconstr(proof) := arewrite [_ * _]proof.

Tactic Notation "arewrite" "-" uconstr(proof) := arewrite -[_ * _]proof.

(* airewrite *)

Tactic Notation "airewrite" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi airewrite_proofgen "lr" (Selected) (proof));
    rewrite 1?mul1x 1?mulx1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "airewrite" "-" "[" ssrpatternarg(pat) "]" uconstr(proof) :=
  ssrpattern pat;
  lazymatch goal with
  |- let _ := ?Selected in _ =>
    let selected := fresh "selected" in
    let proof' := fresh "proof" in
    move=> selected;
    have proof' := ltac:(elpi airewrite_proofgen "rl" (Selected) (proof));
    rewrite 1?mul1x 1?mulx1 in proof';
    rewrite [selected]proof';
    clear selected proof'
  end.

Tactic Notation "airewrite" uconstr(proof) := airewrite [_ * _]proof.

Tactic Notation "airewrite" "-" uconstr(proof) := airewrite -[_ * _]proof.

(* Examples *)

Goal forall M (x y z : M), (x * y) * z = x * (y * z).
Proof.
move=> M x y z.
(* The hand-written reflexive proof in Section 3: *)
exact: (let e1 := ae_mul (ae_mul (ae_var x) (ae_var y)) (ae_var z) in
        let e2 := ae_mul (ae_var x) (ae_mul (ae_var y) (ae_var z)) in
        @areflexivity_correct M e1 e2 erefl).
Qed.

Goal forall M (x y y' z z' : M), y * z = y' * z' -> x * y * z = x * y' * z'.
Proof.
move=> M x x' y y' z H.
Fail rewrite H.
Succeed arewrite H.
Succeed arewrite -[RHS]H.
arewrite [LHS]H.
areflexivity.
(* Reminder: you can type [Show Proof.] to print the generated proof term. *)
Qed.

Goal forall M (a b b' c c' d : M),
  b * c = b' * c' -> a * b * c * d = a * b' * c' * d.
Proof.
move=> M a b b' c c' d H.
Fail rewrite H.
Succeed arewrite H.
Succeed arewrite -[RHS]H.
arewrite [LHS]H.
areflexivity.
Qed.

Goal forall M (x : M) (y : rInvertible M) (z : M), x * y * inv y * z = x * z.
Proof.
move=> M x y z.
arewrite mulxV.
areflexivity.
Restart.
move=> M x y z.
aireflexivity.
Qed.

Goal forall M (a b c : M),
    (forall x, a * x * c = 1) -> b * a * b * b * c * b = b * b.
Proof.
move=> M a b c H.
Fail rewrite H.
arewrite H.
areflexivity.
Qed.

Goal forall M (a : lInvertible M) (b ab : M), a * b = ab -> b = inv a * ab.
Proof.
move=> M a b ab H.
(* The default pattern [_ * _] cannot select the right subterm [b] *)
Fail airewrite H.
(* But, it works if we explicitly select [b]. *)
airewrite [b]H.
done.
Qed.

Goal forall M (b : lInvertible M) (a ab : M), ab * inv b = a -> ab = a * b.
Proof.
move=> M b a ab H.
Fail airewrite H. (* same here *)
airewrite [ab]H.
done.
Qed.

Goal forall M (a : rInvertible M) (b ab : M), inv a * ab = b -> ab = a * b.
Proof.
move=> M a b ab H.
Fail airewrite H. (* same here *)
airewrite [ab]H.
done.
Qed.

Goal forall M (b : rInvertible M) (a ab : M), a * b = ab -> a = ab * inv b.
move=> M b a ab H.
Fail airewrite H. (* same here *)
airewrite [a]H.
done.
Qed.

(* Our reflexive tactics are axiom-free. *)
Print Assumptions all.
