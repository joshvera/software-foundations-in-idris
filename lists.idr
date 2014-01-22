module Lists

%elim data NatPair = MkPair Nat Nat

natFst : NatPair -> Nat
natFst (MkPair a b) = a

natSnd : NatPair -> Nat
natSnd (MkPair a b) = b

pairIsSurjective : (a:Nat) -> (b:Nat) -> (MkPair a b) = (MkPair (natFst (MkPair a b)) (natSnd (MkPair a b)))
pairIsSurjective = ?pairIsSurjectiveCase

pairIsSurjective2 : (p:NatPair) -> p = MkPair (natFst p) (natSnd p)
pairIsSurjective2 = ?pairSurCase

Lists.pairSurCase = proof
  intro
  induction p
  intros
  compute
  trivial

mkNatPair : NatPair -> (Nat,Nat)
mkNatPair (MkPair a b) = (a,b)

surjectivePairingStuck : (a:NatPair) -> a = (MkPair (natFst a) (natSnd a))
surjectivePairingStuck = ?surjectivePairingStuckCase

Lists.surjectivePairingStuckCase = proof
  intros
  induction a
  compute
  intros
  trivial

%elim data NatList =
  Nil
  | Cons Nat NatList

repeat : (n:Nat) -> (count:Nat) -> NatList
repeat n Z = Nil
repeat n (S k) = Cons n (repeat n k)

length : (n:NatList) -> Nat
length Nil = Z
length (Cons x xs) = S (length xs)

app : (a:NatList) -> (b:NatList) -> NatList
app Nil b = b
app (Cons x xs) b = Cons x (app xs b)

syntax [x] "::" [xs] = Cons x xs
syntax "[ ]" = Nil
syntax "[" [x] "]" = (Cons x Nil)
syntax "[" [x] "," rem "," [y] "]" = (Cons x (app rem (Cons y Nil)))
syntax [a] "++" [b] = app a b

head : (default:Nat) -> NatList -> Nat
head n Nil = n
head n (Cons x xs) = x

tail : NatList -> NatList
tail Nil = Nil
tail (Cons x xs) = xs

filterZeros : NatList -> NatList
filterZeros Nil = Nil
filterZeros (Cons Z xs) = filterZeros xs
filterZeros (Cons n xs) = Cons n (filterZeros xs)

testFilterZeros : filterZeros $ Cons 0 (Cons 1 Nil) = (Cons 1 Nil)
testFilterZeros  = refl

oddMembers : NatList -> NatList
oddMembers Nil = Nil
oddMembers (Cons Z xs) = oddMembers xs
oddMembers (Cons x xs) = if (mod x 2) == 1
                            then Cons x (oddMembers xs)
                            else oddMembers xs

testOddMembers : oddMembers $ Cons Z (Cons 1 (Cons 2 Nil)) = (Cons 1 Nil)
testOddMembers = refl

countOddMembers : NatList -> Nat
countOddMembers xs = Lists.length $ oddMembers xs

testCountOddMembers : countOddMembers (Cons Z (Cons 1 (Cons 2 Nil))) = (S Z)
testCountOddMembers = refl

appNilEnd : (xs:NatList) -> app xs Lists.Nil = xs
appNilEnd xs = ?appNilProof

Lists.appNilProof = proof
  intro
  induction xs
  trivial
  intros
  compute
  rewrite ihn__1
  trivial

rCons : (xs:NatList) -> (i:Nat) -> NatList
rCons Nil i = Cons i Lists.Nil
rCons (Cons x xs) i = Cons x (rCons xs i)


rev : NatList -> NatList
rev Nil = Nil
rev (Cons x xs) = rCons xs x

lengthRCons : (n:Nat) -> (xs:NatList) -> length (rCons xs n) = S (length xs)
lengthRCons n xs = ?lengthRConsProof

Lists.lengthRConsProof = proof
  intros
  induction xs
  trivial
  intros
  compute
  rewrite ihn__1
  trivial

revLengthRefl : (xs:NatList) -> length (rev xs) = length xs
revLengthRefl = ?revLengthReflProof

Lists.revLengthReflProof = proof
  intros
  induction xs
  trivial
  intros
  compute
  rewrite (lengthRCons n__0 n__1)
  trivial

revRCons : (xs:NatList) -> (n:Nat) -> rev (rCons xs n) = Cons n (rev xs)
revRCons Lists.Nil n = ?revRConsBaseProof
revRCons xs n = ?revRConsSuccProof

Lists.revRConsBaseProof = proof
  intros
  trivial

revInvolutive : rev $ rev xs = xs
revInvolutive = ?revInvolutiveProof


