-- Overloading + Typeclasses :)

-- typeclasses describe a collection of overloadable operations
-- to overload these ops for a new type, an instance is creaetd that contains an implementation
-- of each operation for the new type.

-- ex: Add describes types that allow addition,
-- and an instance Add Nat provides an implementation for Nats.

--  Unlike Java or C#'s interfaces, types can be given instances for type classes that the author of the type does not have access to.
-- og typeclasses paper: https://dl.acm.org/doi/epdf/10.1145/75277.75283



-- positive numbers

inductive Pos : Type where
  | one : Pos
  | succ : Pos -> Pos

-- this re presents positive nums, but it's not very convenient to use
-- can't use numeric literals

def s : Pos := 7

-- can't use operators
def fourteen : Pos := 7 + 7

-- Classes and Instances
-- a type class consists of a name, params,
-- and a collection of methods.
-- params: types for which overloadable ops are defined
-- methods: names + signatures of overloadable ops

class Plus (α : Type) where
  plus : α -> α -> α
-- type of Plus is Type -> Type

-- now we can "add" two nums
instance : Plus Nat where
  plus := Nat.add
-- methods are defined in a namespace with
-- the name of the typeclass, so let's open
-- it just to not have this be annoying

open Plus (plus)

#eval plus 7 7

-- now to use this typeclass for Pos, we just need
-- to define a plus fn on Pos

def Pos.plus : Pos -> Pos -> Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

#eval plus Pos.one Pos.one

-- no defn for floats, so err
#eval plus 5.2 917.25861

-- Overloading

-- you can overload Lean's add using a typeclass
-- called HAdd.
-- x + y = HAdd.hAdd x y
-- this is general and allows args to have different types

-- we'll implement a simpler one (Add) that requires
-- args to be of the same type. Lean will find this if HAdd is
-- not implemented.

instance : Add Pos where
  add := Pos.plus

def two : Pos := Pos.one + Pos.one

-- Converting to strings
-- used when IO.println is called on a value

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

-- ok, but overwhelming. every pos has a nat,
-- so why not translate them + then render

def Pos.toNat : Pos -> Nat
  | Pos.one => 1
  | Pos.succ n => 1 + n.toNat

instance : ToString Pos where
  toString x := toString (x.toNat)
-- notice, most recent impl for typecalss
-- takes precedence
#eval s!"There are {two}"


def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

-- similar to Add/HAdd, there is Mul/HMul
instance : Mul Pos where
  mul := Pos.mul

-- Literals
-- writing out constructors sucks.
-- we could convert any Nat to a Pos, but:
-- - Poss cannot represent 0, so conversion fn returns Option Pos
-- - you need to call a fn explicitly, not nice. bad api

-- There are 3 classes used to overload numeric literals:
-- Zero
class myZero (α : Type) where
  zero : α
-- One
class myOne (α : Type) where
  one : α
-- OfNat
class myOfNat (α : Type) (_ : Nat) where
  ofNat : α
-- α is the type being overloaded (Pos)
-- the ignored _ Nat arg is the literal we encountered.
-- it is there so that we can only define instances for those
-- values where the number makes sense (ex: 1, 2, 3, 4, ...)

-- this also means that type classes can depend on values, not just types
--  it allows the Lean standard library to arrange for there to be a Zero α instance whenever there's an OfNat α 0 instance, and vice versa

-- let's represent nums less than 4
inductive LT4 where
  | zero
  | one
  | two
  | three

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)

-- out of bound not allowed
#eval (4 : LT4)


-- for Pos, OfNat should work for any Nat
-- other than Nat.zero. we can't write infinitely
-- many cases, so what do?

-- just like α can be an implicit arg to a fn, type classes also
-- take implicit args. Here, the Nat n (mentioned above) is implicit.
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
def zero : Pos := 0 -- can't make it!

-- Exercises

-- another way to rep a pos is as the succ of a Nat.
--
structure Pos2 where
  succ :: -- constructor to make a new struct, recall :)
  pred : Nat

def Pos2.add : Pos2 -> Pos2 -> Pos2
  | p1, p2 => Pos2.succ (1 + p1.pred + p2.pred)

instance: Add Pos2 where
  add := Pos2.add

def Pos2.mul : Pos2 -> Pos2 -> Pos2
  | p1, p2 => Pos2.succ (p1.pred * p2.pred + p1.pred + p2.pred)

instance: Mul Pos2 where
  mul := Pos2.mul

instance : OfNat Pos2 (n) where
  ofNat := {pred := n-1}

instance :  ToString Pos2 where
  toString p := toString (p.pred + 1)

#eval (7 : Pos2)
#eval (2 + 2 : Pos2)
#eval (0 : Pos2) -- evaluates to 1 always, even if it's written '0'
#eval (0 + 0 : Pos2) -- 2 ;)

-- only even numbers
structure Even where
  n : Nat -- the nat we're representing
  pf: n % 2 = 0  -- proof that the nat is even

-- theorem induction₂ (P : Nat → Prop) : P 0 → P 1 → (∀ n, P n → P (n + 2)) → ∀ n, P n := by
--   intro p₀ p₁ p_n n
--   induction n with
--   | zero => exact p₀
--   | succ n' ih =>
--     -- cases n' with
--     -- | zero => simp; exact p₁
--     -- | succ n'' => rw [Nat.add_assoc]; simp; apply p_n; grind;

-- stolen from mathlib: https://github.com/leanprover-community/mathlib4/blob/2d59066e04cb90e9fa4d1393a8cd1ee8ace8daa7/Mathlib/Data/Nat/Init.lean#L273-L278
def twoStepInduction {P : Nat → Prop} (zero : P 0) (one : P 1)
    (more : ∀ n, P n → P (n + 1) → P (n + 2)) : ∀ a, P a
  | 0 => zero
  | 1 => one
  | _ + 2 => more _ (twoStepInduction zero one more _) (twoStepInduction zero one more _)

#check Even.mk 1 (by decide) -- can't make non-even nums

#check Even.mk 2 (by decide) -- CAN make even nums


instance: Add Even where
  add := fun ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ => {
    n := n₁ + n₂
    pf := (by
    -- 'using' keyword for selecting type of induction you want to use
    -- 'generalizing' keyword: quantifies over all n₂, not a fixed term
      induction n₁ using twoStepInduction with
      | zero => simp; exact hn₂
      | one => simp at hn₁
      | more n' ih _ =>
        rw [Nat.add_comm, ← Nat.add_assoc]
        simp at * -- simplify goal and all hypotheses (things that are intro'd)
        rw [Nat.add_comm]
        exact ih hn₁ -- apply ih to hn₁ bc it's a function!
      )
  }

def even2 := Even.mk 2 (by decide)
def even4 := Even.mk 4 (by decide)
#check (even2 +  even4).pf -- safe add




-- An HTTP request begins with an identification of a HTTP method,
--  such as GET or POST, along with a URI and an HTTP version.
--  Define an inductive type that represents an interesting subset of the HTTP methods,
-- and a structure that represents HTTP responses. Responses should have a ToString instance
-- that makes it possible to debug them. Use a type class to associate different IO actions
-- with each HTTP method, and write a test harness as an IO action that calls each method
-- and prints the result.


inductive Request (uri : Type) (body : Type) where
  | GET : uri -> Request uri body
  | POST : uri -> body ->  Request uri body
  | PUT : uri -> body -> Request uri body
  | DELETE : uri -> Request uri body

structure Response where
  status : Int
  body : String

instance : ToString Response where
  toString r := s!"\nRESPONSE:\nStatus: {r.status}\nBody: {r.body}"

class PrintHTTP α where
  runAndPrint : α -> IO Unit

def reqToRes : Request String String -> Response
  | Request.GET _ => {status := 200, body := ""}
  | Request.POST _ body => {status := 200, body := s!"ya posted this: {body}"}
  | Request.PUT _ body => {status := 200, body := s!"ya put this: {body}"}
  | Request.DELETE _ => {status := 200, body := ""}

-- duplication, can we get rid of that?
-- remember, if you want to bind in name then it MUST
-- be written like this
def runAndPrint (req : Request String String): IO Unit :=
  let respond := do IO.println (toString $ reqToRes req)
  match req with
    | Request.GET uri => do
      IO.println s!"GET {uri}"
      respond
    | Request.POST uri body => do
      IO.println s!"POST {uri} {body}"
      respond
    | Request.PUT uri body => do
      IO.println s!"PUT {uri} {body}"
      respond
    | Request.DELETE uri => do
      IO.println s!"DELETE: {uri}"
      respond

instance: PrintHTTP (Request String String) where
  runAndPrint := runAndPrint

#eval do {runAndPrint  (Request.GET "/foo")}
#eval do {runAndPrint (Request.PUT "/foo" "{\"my\":\"body\"}")}
#eval do {runAndPrint (Request.POST "/foo" "{\"my\":\"body\"}")}
#eval do {runAndPrint (Request.DELETE "/foo")}


-- Accepting any instance of a typeclass is denoted by using square brackets
--  the type of IO.println is {α : Type} → [ToString α] → α → IO Unit.

#check @IO.println -- @ supresses Lean's inability to assing concrete values to the type


def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0 -- have to be able to represent some α as 0
  | x :: xs => x + xs.sumOfContents -- have to be able to add αs

def fourNats : List Nat := [1, 2, 3, 4]
#eval fourNats.sumOfContents

def fourPos : List Pos := [1, 2, 3, 4]
#eval fourPos.sumOfContents -- 0 isn't positive, so we violate the typeclass constraint OfNat α 0

-- Specifications of required instances in square brackets are called 'instance implicits'

-- instances themselves can also take instance implicits
structure PPoint (α : Type) where
  x : α
  y : α

-- to add 2 points, we also need to add 2 αs!!
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }


-- this is the true power of type classes. given polymorphic code (using typeclasses) and inputs of
-- of the correct type (that implement the type classes), the compiler will recursively stitch
-- together all the the instances THAT typeclass needs, and that those typeclasses need, and so on.
-- in other languages with overloaded fns, you have to provide all that glue yourself when providing the initial type(s)

-- simpler impl of even
inductive Even2 : Type where
  | zero
  | succ : Even2 → Even2

def evenAdd : Even2 -> Even2 -> Even2
  | Even2.zero, n2  => n2
  | Even2.succ n', n2 => Even2.succ (evenAdd n' n2)


instance : Add Even2 where
 add := evenAdd

-- for showing
def Even2.toNat : Even2 -> Nat
  | Even2.zero => 0
  | Even2.succ n => 2 + n.toNat


instance : ToString Even2 where
  toString x := toString (x.toNat)

-- using recursive typeclass resolution to turn Nats into Evens!!!

-- base case for typeclass resolution
instance : OfNat Even2 0 where
  ofNat := Even2.zero

-- assume OfNat is already satisfied for (Even2, n)
instance [OfNat Even2 n]: OfNat Even2 (n + 2) where
  ofNat := Even2.succ (OfNat.ofNat n) -- get the underlying Even2 by fetching it based on what ofNat returns for n

#check (0 : Even2)
#check (1 : Even2) -- there is no instance for non-even n !!!!!!


-- Controlling instance search

-- can be useful to allow heterogeneous overloading (ex: add Pos + Nat)

def addNatPos : Nat -> Pos -> Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos -> Nat -> Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

-- can do this, ^^ but can't use Add typeclass :(

-- instead, we can use HAdd (3 type params in1 in2 out)
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat)

-- you could have implemented HPlus instead,
-- but it is not as good at inferring the result type.
-- you need to add an explicit type annotation for lean to figure out the type.

class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

-- doesn't work
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat))
-- works
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)

-- we don't want to force users to do this,
-- so this problem can also be solved by declaring γ to be an output parameter.
-- most type class params are inputs to isntance search.
-- others can be specified as 'outputs'; metavariables that will only
-- be solved for once we've started searching.

-- this can be indicated using the outParam modifier
class MyHPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
instance : MyHPlus Nat Pos Pos where
  hPlus := addNatPos
instance : MyHPlus Pos Nat Pos where
  hPlus := addPosNat

#eval MyHPlus.hPlus (3 : Pos) (5 : Nat)

-- Output parameters can determine other types
-- in the program, and instance search can assemble a
-- collection of underlying instances into a program that
-- has this type.

-- Default Instances
-- type class search does not occur until all inputs are known.
-- sometimes we also don't know inputs too, and we want instance
-- search to happen anway! Think optional function arguments, except
-- default TYPES are selected.

-- Default instances are instances that are available
-- for instance search even when not all their inputs
-- are known. if it can be used, it WILL be used.

-- One example of where default instances can be useful is an instance of HPlus that can be derived from an Add instance.
-- normal homogenous addition is just a special case of HAdd
-- where all the types are the same!

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#check HPlus.hPlus (5 : Nat)


-- Exercises

instance [Mul α ] : HMul (PPoint α ) α (PPoint α ) where
  hMul := fun p s => {x := p.x * s, y := p.y * s}

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0

-- Arrays + Indexing

-- random access O(1), contig. area of memory
def northernTrees : Array String :=
 -- #[...]
  #["sloe", "birch", "elm", "oak"]
-- no direct mutation technically, but lean can prove stuff
-- to allow mutations

#eval Array.size northernTrees
#eval northernTrees[1]


structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

-- lookup
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]? -- returns none if out of bounds

-- write as abbrev, bc tactic mode doesn't recognize this name otherwise
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length -- is the access within the bounds?

theorem  eastThreeSpiders : idahoSpiders.inBounds 2 := by
  decide

theorem  notSixSpiders : ¬ idahoSpiders.inBounds 6 := by
  decide

-- now we can write a version that must get a non-empty
-- list at compiletime, and can totally eliminate the Option
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]


-- Exercises

-- class HAppend (α : Type) (β : Type) (γ : outParam Type) where
--   hAppend : α → β → γ

def NonEmptyList.hAppend (as : List α) (bs : NonEmptyList α ) : NonEmptyList α :=
  match as with
    | [] => bs
    | a :: ass => {head := a, tail := ass ++  bs.head :: bs.tail}


instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := NonEmptyList.hAppend


#eval [1,23] ++ ({head := 1, tail := [2]} : NonEmptyList Nat)


-- write a functor instance for bintree

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α


def mapBinTree : (α -> β) -> BinTree α -> BinTree β
  | _, BinTree.leaf => BinTree.leaf
  | f, BinTree.branch l x r => BinTree.branch (mapBinTree f l) (f x) (mapBinTree f r)

instance : Functor (BinTree) where
  map := mapBinTree

def tree := (BinTree.branch (BinTree.branch BinTree.leaf 3 BinTree.leaf) 4 (BinTree.branch BinTree.leaf 2 BinTree.leaf))
#eval mapBinTree toString tree
