module Induction

%default total

plusZeroReduces : (n : Nat) -> n + 0 = n
plusZeroReduces Z = refl
plusZeroReduces (S k) = let ind = plusZeroReduces k in ?plusZeroSucc

Induction.plusZeroSucc = proof
  intros
  rewrite ind
  trivial

minusDiag : (n : Nat) -> minus n n = Z
minusDiag Z = refl
minusDiag (S k) = let ih = minusDiag k in ?minusDiagNeutral

Induction.minusDiagNeutral = proof
  intros
  rewrite ih
  trivial

multZeroIsZero : (n : Nat) -> mult n Z = Z
multZeroIsZero Z = refl
multZeroIsZero (S k) = let ih = multZeroIsZero k in ?multSuccByZeroIsZero

Induction.multSuccByZeroIsZero = proof
  intros
  rewrite ih
  trivial

plusNSuccMRefl : (left : Nat) -> (right : Nat) -> S (left + right) = left + (S right)
plusNSuccMRefl Z right = refl
plusNSuccMRefl (S k) right = let ih = plusNSuccMRefl k right in ?plusSuccRefl

Induction.plusSuccRefl = proof
  intros
  rewrite ih
  trivial

plusCommutes : (left : Nat) -> (right : Nat) -> left + right = right + left
plusCommutes Z right = ?plusCommutesBaseCase
plusCommutes (S left) right = let ih = plusCommutes left right in ?plusCommutesSuccCase

Induction.plusCommutesBaseCase = proof
  intro
  rewrite sym (plusZeroReduces right)
  trivial

Induction.plusCommutesSuccCase = proof
  intros
  rewrite (plusNSuccMRefl right left)
  rewrite ih
  trivial

plusAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + (b + c) = (a + b) + c
plusAssoc Z b c = ?plusAssocBaseCase
plusAssoc (S a) b c = let ih = plusAssoc a b c in ?plusAssocStepCase

Induction.plusAssocBaseCase = proof
  intros
  trivial

Induction.plusAssocStepCase = proof
  intros
  rewrite ih
  trivial

