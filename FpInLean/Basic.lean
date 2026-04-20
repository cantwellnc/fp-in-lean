#eval String.append "a" (String.append "b" "c")

#eval 42 + 19

#eval String.append "A" (String.append "B" "C")
#eval String.append (String.append "A" "B") "C"
#eval if 3 == 3 then 5 else 7
#eval if 3 == 4 then "equal" else "not equal"


#eval (1-2 : Nat)

#eval (1-2 : Int)

#check (1-2 : Int)

-- #check String.append ["hello", ""] ""


-- functions are introed using the 'def' keyword
def helloTo you := String.append "Hello, " you

-- but you can also directly refer to values by names,
-- this is NOT a zero-arg fn
def hello := "Hello"


def joinStringsWithString (s1 : String ) (s2: String) (s3: String) : String :=
  s2 ++ s1 ++ s3

#eval joinStringsWithString "a" "b" "c"


#check joinStringsWithString ":"


def volume (height width depth : Nat) : Nat :=
  height * width * depth


#eval volume 1 2 3


-- defining types

-- alias
def Str : Type := String

-- The reason this works is that types follow the same rules as the rest of Lean.
-- Types are expressions, and in an expression,
-- a defined name can be replaced with its definition.
-- can also use abbrev

abbrev N : Type := Nat


-- structures
-- Defining a structure introduces a completely new type to Lean that can't be reduced to any other type
#check 1.2
#check -454.32324241
-- decimal point => Float
-- otherwise you need a type annotation
#check 0
#check (0 : Float)


-- point

structure Point where
  x : Float
  y : Float

-- constructing
-- note: the type annotation tells lean what structure
-- you are trying to construct
def origin : Point := {x := 0, y:= 0}

#eval origin.x

def addPoints (p1 p2 : Point) : Point :=
  {x := p1.x + p2.x, y := p1.y + p2.y}

-- checking like this is also valid (note the type hint inside the brackets)
#check { x := 0.0, y := 0.0 : Point}

-- updating

def zeroX (p : Point) : Point :=
  {x := 0, y := p.y}
-- naive ^^, if we add a field to point then this defn has
-- to be updated

-- instead, idiomatic way is to use 'with' syntax

def zeroX2 (p : Point) : Point :=
  {p with x:= 0} -- retain all fields of p, only changing x

-- constructors
-- every structure has a built-in constructor. you cannot change it
-- like you can in ex: python

#check Point.mk 1 2 -- for a structure S, this constructor is called mk
-- not good style to use it tho, use brackets

#check Point.mk -- (x y : Float) : Float

-- you can override a constructor's name, but that's it
-- ex: convert Point.mk to Point.point:
structure Point2 where
  point ::
  x : Float
  y : Float

-- the accessors x, y are also fns (but in the structure's namespace)
#check Point.x -- (self : Point) : Float

-- accessor . notation can be used for things other than struct fields
-- you can define it for any type.

-- TARGET.f ARG1 ARG2 ... will substitute TARGET in as left-most arg of T, and then call f with ARG1 ARG2 etc..

-- String is not a struct with a field called 'append', but
-- we can call String.append like this:
#eval "one".append "two" -- "onetwo"


def Point.map (f : Float -> Float) (p : Point ) : Point :=  -- note: p is not leftmost, but there's only one place to put it
  {x := f p.x, y := f p.y}

def fourAndThree : Point := {x := 4, y := 3}

#eval fourAndThree.map Float.sin


-- exercises

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def volume2 (p : RectangularPrism) : Float :=
  p.height * p.width * p.depth

#eval volume2 ({height := 2, width := 1 , depth := 2 : RectangularPrism})


structure Segment where
  lSide : Float
  rSide : Float

def length (s : Segment) : Float :=
  s.rSide - s.lSide

#eval length ({lSide := 0, rSide := 1 : Segment})

-- RectangularPrism intros: RectangularPrism.{mk, depth, width, heigh}


-- structures are known as product types.
-- data structures that allow choices are sum types.
-- data structures that can include instances of themselves are recursive datatypes.
-- recursive sum types are called INDUCTIVE datatypes.

-- Bool is inductive
inductive MyBool where
  | false : MyBool -- each of these are type constructors
  | true : MyBool

-- note that you may have multiple constructors for a single
-- inductive dt, UNLIKE structures.
-- constructors are placed in the namespace of the type, just like structures.


-- Natural numbers are also inductive

inductive MyNat where
  | zero : MyNat -- you're either 0
  | succ (n : MyNat) : MyNat -- or 1 + (a natural number)

#eval (Nat.succ (Nat.succ (Nat.succ Nat.zero)) = 3)


-- pattern matching

def isZero (n : Nat) : Bool :=
  match n with
    | Nat.zero => true
    | Nat.succ k => false

#eval isZero 0
#eval isZero 1


-- predecessor
def pred (n : Nat) : Nat :=
  match n with
    | Nat.zero => n
    | Nat.succ k => k

#eval (pred 2 = 1) -- equality check
-- same thing: is the proposition (pred 2 = 1) true?
#eval (pred 2 = 1 : Prop) = true

#eval pred 0 -- 0

-- you can match on structs too!

def depth (p : RectangularPrism) : Float :=
  match p with
    | {height := _, width := _, depth := d} => d
    -- you can't use {p with depth := d} tho :(


-- recursive fns are good for dealing w recursive data

def even (n : Nat) : Bool :=
  match n with
    | Nat.zero => true
    | Nat.succ k => not (even k) -- wow that is beautiful
-- this type of fn is known as doing "structural recursion" since we specify what to do
-- for each constructor of Nat


-- lean will reject infinitely looping programs like this one that accidentally
-- calls even with the original number instead of k
def evenLoop (n : Nat) : Bool := -- "failed to show termination"
  match n with
    | Nat.zero => true
    | Nat.succ _ => not (evenLoop n)
-- lean wants every function to provably terminate by reaching a base case when
-- doing structural recursion


def add (n k : Nat) : Nat :=
  match k with
    | Nat.zero => n
    | Nat.succ k' => Nat.succ (add n k')
-- n + k = succ(succ(... k times ... (n)))


def mult (n k : Nat) : Nat :=
  match k with
    | Nat.zero => Nat.zero -- add n to itself k times
    | Nat.succ k' => add n (mult n k') -- n + n*k-1

#eval mult 3 4


-- div is not structurally recursive so lean can't prove that it terminates.
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then -- not matching on constructors!
    0
  else Nat.succ (div (n - k) k) -- arg is


-- polymorphism

--let's make a polymorphic point that can use floats or ints or whatever

structure PPoint (α : Type) where
  x : α
  y : α

-- you can concretize to a particular type

def origin2 : PPoint Nat := { x:= 0, y:=0 }
#check origin2

-- defns can take types are arguments, so they are also polymorphic.

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  {point with x:= newX}
-- Polymorphic functions work by taking a named type argument and having later types refer to the argument's name.
-- there's no ad-hoc reason for how types can be named + passed around.
-- lean can compute on types! for instance, we can write the type for a function
-- that takes a Sign (pos | neg) will return a nat or an int depending on the sign.

inductive Sign where
 | pos
 | neg

def posOrNegThree (s : Sign) :
  match s with | Sign.pos => Nat | Sign.neg => Int
  -- whaaaaaat, you can pattern match in the type signature
  :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

-- question: can i write the type of this function separetly from
-- the impl? I can't seem to find the right way to do so..

-- Linked lists
-- The List dt in lean has a special syntax.

def primesUnder10 : List Nat := [2,3,5,7]

-- List is inductive
inductive myList (α : Type) where
  | nil : myList α
  | cons : α -> myList α -> myList α

-- so [...] is a nicer way to write cons(cons(cons ... (nil)))


def length2 (α : Type) (xs : List α ) : Nat :=
  match xs with
    | List.nil => 0
    | List.cons _ ys => Nat.succ (length2 α ys)

#eval length2 Int [1,2,3]


-- or alternate syntax for pattern matching on lists:

def length3 (α : Type) (xs : List α ) : Nat :=
  match xs with
    | [] => 0
    | y :: ys => Nat.succ (length3 α ys)


-- it's good style to put type parameters as 'implicit' arguments
def length4 {α : Type} (xs : List α ) : Nat :=
  match xs with
    | [] => 0
    | _ :: ys => Nat.succ (length4 ys)

-- now when calling lean will just infer the value of α
-- without us having to explicitly pass the type as an
-- argument
#check length4 [1, 2,3] -- Nat


-- more builtin datatypes
-- Option

inductive myOption (α : Type) : Type where
  | none : myOption α -- nothing
  | some (val : α): myOption α -- or something or type α


-- ex: find head of list, if it exists
def head? {α : Type} (xs : List α ) : Option α :=
  match xs with
    | List.nil => Option.none
    | y :: _ => Option.some y


-- the real lean fn is List.head?, ? indicates option (just a convention)


-- naming conventions!!!
-- returns Option = myFun?
-- crashes on invalid input = myFun!
-- provides default when only option is failure = myFunD


-- Prod structure
-- generic way of joining values of two types together.

structure myProd (α β : Type) : Type where
  fst: α
  snd:  β
-- elems are (a ∈ α, b ∈ β )

-- the builtin type Prod is usually written α × β
def fives : (String × Int) := {fst := "five", snd := 5}
-- but you can use an alternative constructor for less boilerplate
def fives2 : (String × Int) := ("five", 5)

-- both are right associative, so these are equal
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
def sevens2 : String × (Int × Nat) := ("VII", (7, 4 + 3))
#eval sevens = sevens2

-- Sum
-- allows choice between multiple values of two types

inductive mySum (α β : Type) : Type where
  | inl : α -> mySum α β
  | inr : β -> mySum α β

-- another notation is α ⊕ β
-- dog or cat names
def PetName : Type := String ⊕ String

-- in real programs, it's better to define a custom inductive
-- type rather than using Sum

-- can construct dog / cat names
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]

-- and match on them

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: rest => howManyDogs rest + 1
  | Sum.inr _ :: rest => howManyDogs rest
-- Function calls are evaluated before infix operators, so howManyDogs morePets + 1 is the same as (howManyDogs morePets) + 1


-- Unit
-- a type with one argless constructor, called unit.
-- It describes a single value, constructed by calling the argless
-- constructor.


-- the proposition that is always true
inductive myUnit : Type where
  | unit : myUnit

-- can be useful for data that is missing in polymorphic code.

-- Additionally, because all Lean functions have arguments,
-- zero-argument functions in other languages can be represented as
-- functions that take a Unit argument.

-- In a return position, the Unit type is similar to void in languages derived from C.


-- Empty
-- The Empty dt has no constructrors. It represents unreachable code.
-- no series of calls can ever terminate with a value at type Empty.


--- warnings:

-- Not all definable structures or inductive types can have the type Type.

-- ex: In particular, if a constructor takes an ARBITRARY type as an argument,
-- then the inductive type must have a different type.
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType
  -- illegal for now
-- instead, make type take it as param

inductive MyType2 (α : Type) : Type where
  | ctor : α -> MyType2 α -- don't forget type arg to type itself!

-- legit when we provide a type arg ex: Nat
def ofFive : MyType2 Nat := MyType2.ctor 5

-- err: MyType2 : Type -> Type
def ofFive2 : MyType2 := MyType2.ctor 5


-- sometimes lean can't display stuff using eval. usually
-- it will try and generate display code from the type of the expr,
-- but for some types (ex: functions) this fails.
-- this works fine:

inductive WoodSplitters where
  | axe
  | maul
  | froe

#eval WoodSplitters.axe

-- but this won't
def allTools : List WoodSplitters := [
  WoodSplitters.axe,
  WoodSplitters.froe,
  WoodSplitters.maul
]

#eval allTools -- tries to display list, and list wants display
-- code for WoodSplitters to already exist, but Lean hasn't generated
-- it yet :(

-- you can make it gen the code ahead of time (instead of at eval time)
-- by adding deriving Repr to your type defn.

inductive Firewood where
  | birch
  | pine
  | beech
  deriving Repr -- yay

def allWoods : List Firewood := [
  Firewood.beech,
  Firewood.pine,
  Firewood.birch
]

#eval allWoods -- all good

-- exercises

-- last entry in a list
def last? {α : Type} (xs : List α): Option α :=
  match xs with
  | [] => Option.none
  | y :: [] => Option.some y
  | _ :: ys => last? ys

#eval last? ([]: List Nat)
#eval last? [1, 2, 3]

-- first entry in list that satisfies pred p
def List.findFirst? {α : Type} (xs : List α ) (pred : α -> Bool) : Option α :=
  match xs with
  | [] => Option.none
  | y :: ys => if pred y then Option.some y else List.findFirst? ys pred

#eval [1,2,3].findFirst? even -- 2
#eval [].findFirst? even -- none


-- switch two fields in a pair

def Prod.switch {α β : Type} (pair : α × β ): β × α  :=
  match pair with
  | (a, b) => (b, a)

#eval (1, "two").switch

-- rewrite petname to be a custom inductive type instead of a sum
inductive PetName2 where
  | dog (name : String) : PetName2
  | cat (name : String) : PetName2

#eval PetName2.dog "Joe"

-- zip: combine two lists into a pair of lists
-- as long as shorter input list
def zip {α β  : Type} (xs: List α) (ys : List β ): List (α × β) :=
  match xs, ys with
  | _, [] => List.nil
  | [] ,_ => List.nil
  | x' :: xs', y' :: ys' => (x', y') :: zip xs' ys'

#eval zip ([] : List Nat) [1]
#eval zip [1] ([] : List Nat)
#eval zip [1] ["2", "3"]
#eval zip ["2", "3"] [1]
#check zip [1] ["2", "3"]


-- take first n
def take {α : Type} (n : Nat) (xs: List α ) : List α :=
  match n, xs with
  | Nat.zero, _ => []
  | _, [] => []
  | Nat.succ n', y :: ys => y :: take n' ys


#eval take 2 [1, 2, 3]
#eval take 2 ([] : List Nat)
#eval take 0 [1,2]


-- distribute products over sums
def dist {α β γ : Type} (x : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match x with
  | (a, y) =>
    match y with
    | Sum.inl b => Sum.inl (a, b)
    | Sum.inr g => Sum.inr (a, g)

#check dist (1, (Sum.inl "Leo" : String ⊕ String))

-- using analogy between types and arithmetic,
-- turning multiplying by 2 into a sum

def mul {α : Type} (b: Bool) (a: α ) : α ⊕ α :=
  match b with
  | true => Sum.inl a
  | false => Sum.inl a


-- Additional conveniences

-- Implicit type params {α : Type} can often be omitted. makes
-- highly polymorphic defns more readable.


-- it's quite common to name an argument and then immediately use it with pattern matching.

--  For instance, in length, the argument xs is used only in match.
-- In these situations, the cases of the match expression can be written directly,
--  without naming the argument at all.

def length5 : List α -> Nat
  | [] => 0
  | _ :: ys => Nat.succ (length5 ys)

-- can also be used with fns that take more than one arg
def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, _ :: xs => drop n xs

-- you can mix and match
def fromOption (default : α ) : Option α -> α
  | none => default
  | some x => x

-- stdlib version is Option.getD

-- Local Definitions
-- consider this
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip xys).fst, y :: (unzip xys).snd)
    -- two recursive calls, but same value
-- instead, use let!

def unzip2 : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys -- yay, computed once
    (x :: unzipped.fst, y :: unzipped.snd)


-- The biggest difference between let and def is that
-- recursive let definitions must be explicitly indicated by writing let rec.
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α -- ex
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

-- simul matching is NOT the same as matchin on a pair. Lean tracks
-- additional info in the latter case.

-- this cannot be proven to terminate bc we match on
-- (xs, ys) rather than xs, ys which prevents lean from
-- using structural recursion to show the fn terminates.
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false

-- Nats can also be matched against directly. no need to use constructors
def even3 : Nat -> Bool
  | 0 => true
  | n + 1 => not (even3 n)


-- When using this syntax, the second argument to + should always be a literal Nat.
-- Even though addition is commutative, flipping the arguments
-- in a pattern can result in errors like the following:

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 + n => halve n + 1


-- Lambdas
#check fun x => x + 1
#check fun (x : Int)  => x + 1
#check fun {α : Type} (x : α ) => x
-- really simple ones can be written like this:
#check (. + 1)
-- creates a fn out of the closest set of parens
#check (. + 5, 3)
#check ((. + 5), 3)
#eval (., .) 1 2


-- Namespaces
-- defined using ., ex. List.map vs. Array.map
-- can def a fn in a namespace
def Nat.double (x : Nat) : Nat := x + x

-- or can create a namespace
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

-- open it (use names without qualification)
def timesTwelve (x : Nat) :=
  open NewNamespace in -- makes ns available in the following expr
  quadruple (triple x)

-- Namespaces may additionally be opened for all following commands for the rest of the file,
-- just omit 'in'

-- if let is a thing (need then/else clauses still tho)

-- string interp
#eval s! "6 {5 + 2}"
-- doesn't work with every expr
#eval s! "6 {NewNamespace.triple}" -- no std way to convert fns to strings

-- Just as the compiler maintains a table that describes how to display the
-- result of evaluating expressions of various types, it maintains a table
-- that describes how to convert values of various types into strings.
--  The message failed to synthesize instance means that the Lean compiler
-- didn't find an entry in this table for the given type.

--  Pattern matching means that knowing how to create a value implies knowing how to consume it.
