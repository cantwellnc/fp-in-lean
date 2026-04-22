-- Lean can express many types, including the type of Propositions

-- here 1+2 = 2 is a TYPE!!
def onePlusOneIsTwo : 1 + 1 = 2 := rfl

-- you can "prove" a propostion by providing evidence that it is true.

-- ex: using the 'rfl' constructor for =

-- when you prove stuff you typically call it a theorem
theorem onePlusOneIsTwo2 : 1 + 1 = 2 := rfl
-- the way you provide evidence doesn't matter to lean
-- as long as you provide everything that is needed to
-- check the theorem

-- theorems are usually proved using 'tactics', which are progams
-- that construct evidence for proofs.
-- you drop into tactic mode by using 'by'

theorem onePlusOneIsTwo3 : 1 + 1 = 2 := by
  decide -- invokes a 'decision procedure' that will return T/F
  -- of the given statement.

  -- big hammer; others include simp / grind

-- you can think of tactics as fns (Available Assumptions, Proof State) -> (Available Assumptions, Proof State)

-- simp re-writes goals into the simplest form it can find
-- grind is used to finish proofs. it cannot make progress without
-- completing the proof entirely (unlike simp); it either succeeds or fails


-- Connectives
-- and or not true false

--  If A and B are propositions, then “A and B” (written A ∧ B) is a proposition.
-- Evidence for A ∧ B consists of A SINGLE constructor And.intro,
-- which has the type A → B → A ∧ B. there is no other way to get evidence for this.

-- Replacing A and B with concrete propositions, it is possible to prove
--  1 + 1 = 2 ∧ "Str".append "ing" = "String"
-- with  And.intro rfl rfl.

theorem t1 : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := And.intro rfl rfl

-- A ∨ B is written similarly, and has 2 constructors Or.inl and Or.inr

-- Implication is represented using functions. Evidence that A implies B
-- is just a function that transforms evidence for A into evidence for B.


-- bc these are all datatypes, you can pattern match + reshape the data!

theorem andImpliesOr : A ∧ B -> A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a -- so cool

-- ¬A is a function that would transform evidence of A into evidence of False
-- False has no evidence.
-- True's evidence is True.intro : True

-- decide can prove theorems using these connectives


-- Evidence as Arguments
-- in general, this fn is not safe
def third (xs : List α) : α := xs[2]
-- we don't know xs, so could be [1,2] or [1] or []


-- but we could define it to take a proof that len xs > 2
def third2 (xs : List α ) (ok : xs.length > 2) := xs[2]
-- ok is evidence that the proposition is TRUE. the fn
-- itself is not doing any checking.
-- something else needs to provide the evidence, for example decide

#eval third2 [1, 2, 3] (by decide) -- constructs the proof on the fly
#eval third2 [1, 2] (by decide) -- decide proves false, so type err


-- only programs whose types contain at least one value are allowed to crash
def unsafeThird (xs : List α) : α := xs[2]! -- get idx or crash
-- this program doesn't compile bc we don't know α.
-- if we subbed in False for α, and such programs are allowed to crash (they always would),
-- then we could manufacture evidence for false props by just writing crashing programs of the
-- type we need :)

-- Exercises
theorem a : (2 + 3 = 5) := rfl
theorem b : ("Hello ".append "World!" = "Hello World!") := rfl
theorem c : (5<18) := rfl -- rfl could not prove this bc it can only make stuff of type a = a

theorem a' : (2 + 3 = 5) := by decide
theorem b' : ("Hello ".append "World!" = "Hello World!") := by decide
theorem c' : (5 < 18) := by decide

def lookupFifth (xs : List α ) (ok : xs.length > 4) := xs[4]
#eval lookupFifth [1,2,3,4,5] (by decide)
