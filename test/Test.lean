/-
  Tests for ExtendedDeriveDecEq: verify that derive_deceq produces computable
  DecidableEq for various mutual/nested inductive configurations.
  The compilability defs are the real test — if the DecidableEq instance
  exists and compiles, correctness is kernel-guaranteed.
-/
import ExtendedDeriveDecEq


-- ============================================================
-- Test 1: Simple mutual (no nesting)
-- ============================================================
namespace Test1

mutual
inductive A where | mkA : B → A
inductive B where | mkB : A → B | leaf : B
end

derive_deceq A

def testA (a b : A) : Bool := a == b
def testB (a b : B) : Bool := a == b

#guard A.mkA B.leaf == A.mkA B.leaf
#guard !(A.mkA B.leaf == A.mkA (B.mkB (A.mkA B.leaf)))

end Test1

-- ============================================================
-- Test 2: Three-way mutual (no nesting)
-- ============================================================
namespace Test2

mutual
inductive X where | fromY : Y → X | xLeaf : Nat → X
inductive Y where | fromZ : Z → Y | yLeaf : Y
inductive Z where | fromX : X → Z | zLeaf : Bool → Z
end

derive_deceq X

def testX (a b : X) : Bool := a == b
def testY (a b : Y) : Bool := a == b
def testZ (a b : Z) : Bool := a == b

#guard X.xLeaf 42 == X.xLeaf 42
#guard !(Z.zLeaf true == Z.zLeaf false)

end Test2

-- ============================================================
-- Test 3: Single inductive with List nesting
-- ============================================================
namespace Test3

inductive Tree where | node : List Tree → Tree | tip : Nat → Tree

derive_deceq Tree

def testTree (a b : Tree) : Bool := a == b

#guard Tree.node [Tree.tip 1, Tree.tip 2] == Tree.node [Tree.tip 1, Tree.tip 2]
#guard !(Tree.node [Tree.tip 1] == Tree.node [Tree.tip 2])

end Test3

-- ============================================================
-- Test 4: Parametric mutual with List/Option nesting and type parameter
-- ============================================================
namespace Test4

variable (t : Type) [DecidableEq t]

mutual
inductive Expr where
  | lit : t → Expr
  | app : Expr → List Expr → Expr
  | lam : List Param → Expr → Expr
  | cond : Expr → Expr → Option Expr → Expr
  | typed : Typed → Expr
inductive Param where
  | mk : String → Ty → Option Expr → Param
inductive Ty where
  | base : String → Ty
  | arrow : List Ty → Ty → Ty
inductive Typed where
  | ann : Expr → Ty → Typed
end

derive_deceq Expr

end Test4

-- ============================================================
-- Test 5: Multiple List-wrapped types in one block
-- ============================================================
namespace Test5

mutual
inductive Stmt where
  | block : List Stmt → Stmt
  | assign : String → Val → Stmt
inductive Val where
  | num : Int → Val
  | arr : List Val → Val
  | record : List Field → Val
inductive Field where
  | mk : String → Val → Field
end

derive_deceq Stmt

def testStmt (a b : Stmt) : Bool := a == b
def testVal (a b : Val) : Bool := a == b
def testField (a b : Field) : Bool := a == b

#guard Val.arr [Val.num 1, Val.num 2] == Val.arr [Val.num 1, Val.num 2]
#guard !(Val.arr [Val.num 1] == Val.arr [Val.num 2])

end Test5

-- ============================================================
-- Test 6: Multi-constructor types with mixed fields
-- ============================================================
namespace Test6

mutual
inductive Term where
  | var : Nat → Term
  | abs : Nat → Tp → Term → Term
  | app : Term → Term → Term
inductive Tp where
  | unit : Tp
  | fn : Tp → Tp → Tp
  | forall_ : List Tp → Tp → Tp
end

derive_deceq Term

def testTerm (a b : Term) : Bool := a == b
def testTp (a b : Tp) : Bool := a == b

#guard !(Term.var 0 == Term.app (Term.var 0) (Term.var 1))
#guard Tp.forall_ [Tp.unit] Tp.unit == Tp.forall_ [Tp.unit] Tp.unit

end Test6

-- ============================================================
-- Test 7: Zero-field constructors and singleton types
-- ============================================================
namespace Test7

mutual
inductive Tag where | a | b | c
inductive Wrap where | mk : Tag → Wrap
end

derive_deceq Tag

def testTag (x y : Tag) : Bool := x == y
def testWrap (x y : Wrap) : Bool := x == y

#guard !(Tag.a == Tag.b)
#guard Wrap.mk Tag.a == Wrap.mk Tag.a

end Test7

-- ============================================================
-- Test 8: Option nesting (non-List container)
-- ============================================================
namespace Test8

mutual
inductive Config where
  | mk : Option Config → Nat → Config
inductive Pair where
  | mk : Config → Config → Pair
end

derive_deceq Config

def testConfig (a b : Config) : Bool := a == b
def testPair (a b : Pair) : Bool := a == b

#guard Config.mk (some (Config.mk none 0)) 1 ==
       Config.mk (some (Config.mk none 0)) 1
#guard !(Config.mk (some (Config.mk none 0)) 1 ==
         Config.mk none 1)

end Test8

-- ============================================================
-- Test 9: Mixed List + Option nesting
-- ============================================================
namespace Test9

inductive Node where
  | leaf : Nat → Node
  | branch : List Node → Option Node → Node

derive_deceq Node

def testNode (a b : Node) : Bool := a == b

#guard Node.branch [Node.leaf 1] (some (Node.leaf 2)) ==
       Node.branch [Node.leaf 1] (some (Node.leaf 2))
#guard !(Node.branch [Node.leaf 1] none ==
         Node.branch [Node.leaf 1] (some (Node.leaf 2)))

end Test9

-- ============================================================
-- Test 10: Custom container (not built-in List/Option)
-- Ensures the deriver doesn't rely on built-in DecidableEq instances.
-- ============================================================
namespace Test10

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

inductive Expr2 where
  | lit : Nat → Expr2
  | add : Expr2 → Expr2 → Expr2
  | block : MyList Expr2 → Expr2

derive_deceq Expr2

def testExpr2 (a b : Expr2) : Bool := a == b

#guard Expr2.block (.cons (Expr2.lit 1) .nil) ==
       Expr2.block (.cons (Expr2.lit 1) .nil)
#guard !(Expr2.block (.cons (Expr2.lit 1) .nil) ==
         Expr2.block .nil)

end Test10

-- ============================================================
-- Test 11: Parametric mutual inductive (type parameter α)
-- ============================================================
namespace Test11

mutual
inductive Foo (α : Type) where
  | leaf : α → Foo α
  | node : Bar α → Foo α
inductive Bar (α : Type) where
  | single : Foo α → Bar α
  | pair : Foo α → Foo α → Bar α
end

derive_deceq Foo

def testFoo (a b : Foo Nat) : Bool := a == b
def testBar (a b : Bar Nat) : Bool := a == b

#guard Foo.leaf 1 == Foo.leaf 1
#guard !(Bar.pair (Foo.leaf 1) (Foo.leaf 2) == Bar.pair (Foo.leaf 1) (Foo.leaf 3))

end Test11

-- ============================================================
-- Test 12: Parametric with List nesting
-- ============================================================
namespace Test12

inductive Tree (α : Type) where
  | tip : α → Tree α
  | node : List (Tree α) → Tree α

derive_deceq Tree

def testTree (a b : Tree String) : Bool := a == b

#guard Tree.node [Tree.tip "a", Tree.tip "b"] == Tree.node [Tree.tip "a", Tree.tip "b"]
#guard !(Tree.node [Tree.tip "a"] == Tree.node [Tree.tip "b"])

end Test12

-- ============================================================
-- Test 13: Mutual + deep nesting + custom container
-- (List, List-of-List, List-of-List-of-List, custom MyList, mutual MLabel)
-- ============================================================
namespace Test13

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

mutual
inductive MTree where
  | leaf : Nat → MTree
  | container : List MTree → MTree
  | nested : List (List MTree) → MTree
  | deep : List (List (List MTree)) → MTree
  | mixed : List (Option (MyList MTree)) → MTree
  | labelled : MLabel → MTree
inductive MLabel where
  | named : String → MTree → MLabel
  | multi : List MLabel → MLabel
end

derive_deceq MTree

def testMTree (a b : MTree) : Bool := a == b
def testMLabel (a b : MLabel) : Bool := a == b

-- List
#guard MTree.container [.leaf 1, .leaf 2] == MTree.container [.leaf 1, .leaf 2]
#guard !(MTree.container [.leaf 1] == MTree.container [.leaf 2])
-- List (List _)
#guard MTree.nested [[.leaf 1], [.leaf 2, .leaf 3]] ==
       MTree.nested [[.leaf 1], [.leaf 2, .leaf 3]]
#guard !(MTree.nested [[.leaf 1]] == MTree.nested [[.leaf 2]])
-- List (List (List _))
#guard MTree.deep [[[.leaf 1], [.leaf 2]], [[.leaf 3]]] ==
       MTree.deep [[[.leaf 1], [.leaf 2]], [[.leaf 3]]]
#guard !(MTree.deep [[[.leaf 1]]] == MTree.deep [[[.leaf 2]]])
-- cross-constructor
#guard !(MTree.container [.leaf 1] == MTree.nested [[.leaf 1]])
-- mixed: List (Option (MyList _))
#guard MTree.mixed [some (.cons (.leaf 1) .nil), none] ==
       MTree.mixed [some (.cons (.leaf 1) .nil), none]
#guard !(MTree.mixed [some (.cons (.leaf 1) .nil)] ==
         MTree.mixed [some (.cons (.leaf 2) .nil)])
#guard !(MTree.mixed [some .nil] == MTree.mixed [none])
-- mutual: MLabel
#guard MLabel.named "x" (.leaf 1) == MLabel.named "x" (.leaf 1)
#guard !(MLabel.named "x" (.leaf 1) == MLabel.named "y" (.leaf 1))
#guard MLabel.multi [.named "a" (.leaf 1), .named "b" (.leaf 2)] ==
       MLabel.multi [.named "a" (.leaf 1), .named "b" (.leaf 2)]
#guard !(MLabel.multi [.named "a" (.leaf 1)] == MLabel.multi [.named "a" (.leaf 2)])
-- round-trip: MTree containing MLabel containing MTree
#guard MTree.labelled (.named "root" (.container [.leaf 1])) ==
       MTree.labelled (.named "root" (.container [.leaf 1]))
#guard !(MTree.labelled (.named "root" (.leaf 1)) ==
         MTree.labelled (.named "root" (.leaf 2)))

end Test13

-- ============================================================
-- Indexed family tests
-- ============================================================


-- ============================================================
-- Test I1: Indexed + parametric (α parameter + Nat index)
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI1

inductive ParamVec (α : Type) : Nat → Type where
  | nil : ParamVec α 0
  | cons : α → ParamVec α n → ParamVec α (n + 1)

derive_deceq ParamVec

def test (a b : ParamVec Nat n) : Bool := a == b

#guard ParamVec.nil == (ParamVec.nil : ParamVec Nat 0)
#guard ParamVec.cons 1 .nil == ParamVec.cons 1 .nil
#guard !(ParamVec.cons 1 .nil == ParamVec.cons 2 .nil)
#guard ParamVec.cons "a" (.cons "b" .nil) == ParamVec.cons "a" (.cons "b" .nil)
#guard !(ParamVec.cons "a" (.cons "b" .nil) == ParamVec.cons "a" (.cons "c" .nil))

end TestI1

-- ============================================================
-- Test I2: Indexed + parametric + nested (List) with same index.
-- The kernel promotes a same-index field-and-return position into
-- a parameter, so this looks non-indexed to the deriver.
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✗ (nested)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI2

inductive Forest (α : Type) : Nat → Type where
  | leaf : α → Forest α n
  | branch : List (Forest α n) → Forest α n

derive_deceq Forest

#guard Forest.leaf 1 == (Forest.leaf 1 : Forest Nat 0)
#guard !(Forest.leaf 1 == (Forest.leaf 2 : Forest Nat 0))
#guard Forest.branch [Forest.leaf "a", Forest.leaf "b"]
    == (Forest.branch [Forest.leaf "a", Forest.leaf "b"] : Forest String 5)
#guard !(Forest.branch [Forest.leaf "a"] == (Forest.branch [Forest.leaf "b"] : Forest String 5))

end TestI2

-- ============================================================
-- Test I3: Indexed by a custom enum (non-Nat index)
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI3

inductive Phase where | parse | check | emit
  deriving DecidableEq

inductive IR : Phase → Type where
  | raw : String → IR .parse
  | typed : Nat → IR .check
  | code : String → Nat → IR .emit

derive_deceq IR

#guard IR.raw "hello" == IR.raw "hello"
#guard !(IR.raw "a" == IR.raw "b")
#guard IR.typed 42 == IR.typed 42
#guard !(IR.typed 1 == IR.typed 2)
#guard IR.code "x" 1 == IR.code "x" 1
#guard !(IR.code "x" 1 == IR.code "y" 1)
#guard !(IR.code "x" 1 == IR.code "x" 2)

end TestI3

-- ============================================================
-- Test I4: Indexed with many constructors (stress test)
-- Single index, 6 constructors spread across 3 index values.
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI4

inductive MultiCtor : Nat → Type where
  | a0 : MultiCtor 0
  | b0 : Nat → MultiCtor 0
  | a1 : String → MultiCtor 1
  | b1 : MultiCtor 1
  | a2 : Nat → Nat → MultiCtor 2
  | b2 : String → MultiCtor 2

derive_deceq MultiCtor

#guard MultiCtor.a0 == MultiCtor.a0
#guard !(MultiCtor.a0 == MultiCtor.b0 5)
#guard MultiCtor.b0 3 == MultiCtor.b0 3
#guard !(MultiCtor.b0 3 == MultiCtor.b0 4)
#guard MultiCtor.a1 "x" == MultiCtor.a1 "x"
#guard !(MultiCtor.a1 "x" == MultiCtor.b1)
#guard MultiCtor.a2 1 2 == MultiCtor.a2 1 2
#guard !(MultiCtor.a2 1 2 == MultiCtor.a2 1 3)
#guard !(MultiCtor.a2 1 2 == MultiCtor.b2 "z")

end TestI4

-- ============================================================
-- Test I5: Indexed type with one Prop-typed field.
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI5

axiom WF : Nat → Prop

inductive Checked : Nat → Type where
  | mk : (val : Nat) → WF n → Checked n

derive_deceq Checked

end TestI5

-- ============================================================
-- Test I6: Recursive indexed (Fin-like with predecessor)
-- Single-index, each constructor builds from predecessor index.
-- Tests binary number representation (Bits n = n-bit strings).
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI6

inductive Bits : Nat → Type where
  | done : Bits 0
  | zero : Bits n → Bits (n + 1)
  | one : Bits n → Bits (n + 1)

derive_deceq Bits

#guard Bits.done == Bits.done
#guard Bits.zero .done == Bits.zero .done
#guard !(Bits.zero .done == Bits.one .done)
#guard Bits.one (.zero .done) == Bits.one (.zero .done)
#guard !(Bits.one (.zero .done) == Bits.one (.one .done))
-- 3-bit: 101 vs 110
#guard !(Bits.one (.zero (.one .done)) == Bits.one (.one (.zero .done)))

end TestI6

-- ============================================================
-- Test I7: Two-index + parametric + index-changing recursion
-- The `row` constructor has field `Grid α m n` but returns
-- `Grid α (m+1) 0` — free index `n` gets separate a/b binders
-- in the casesOnSameCtor minor, requiring subst before comparing
-- the recursive field.
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI7

inductive Grid (α : Type) : Nat → Nat → Type where
  | empty : Grid α 0 0
  | cell : α → Grid α m n → Grid α m (n + 1)
  | row : Grid α m n → Grid α (m + 1) 0

derive_deceq Grid

#guard (Grid.empty : Grid Nat 0 0) == Grid.empty
#guard Grid.cell 1 .empty == Grid.cell 1 .empty
#guard !(Grid.cell 1 .empty == Grid.cell 2 .empty)
#guard Grid.row (.cell 1 .empty) == Grid.row (.cell 1 .empty)
#guard !(Grid.row (.cell 1 .empty) == Grid.row (.cell 2 .empty))
#guard Grid.row (.empty : Grid Nat 0 0) == Grid.row .empty

end TestI7

-- ============================================================
-- Test I8: Non-recursive indexed (all constructors produce
-- fixed index values; no recursive fields)
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI8

inductive Token : Bool → Type where
  | keyword : String → Token true
  | ident : String → Token false
  | number : Nat → Token false

derive_deceq Token

#guard Token.keyword "if" == Token.keyword "if"
#guard !(Token.keyword "if" == Token.keyword "else")
#guard Token.ident "x" == Token.ident "x"
#guard !(Token.ident "x" == Token.number 5)
#guard Token.number 42 == Token.number 42

end TestI8

-- ============================================================
-- Test I9: Indexed + Option nesting with same index.
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✗ (nested)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI9

inductive OptTree : Nat → Type where
  | leaf : Nat → OptTree n
  | node : Nat → Option (OptTree n) → Option (OptTree n) → OptTree n

derive_deceq OptTree

#guard OptTree.leaf 1 == (OptTree.leaf 1 : OptTree 0)
#guard !(OptTree.leaf 1 == (OptTree.leaf 2 : OptTree 0))
#guard OptTree.node 1 none none == (OptTree.node 1 none none : OptTree 0)
#guard OptTree.node 1 (some (.leaf 2)) none == (OptTree.node 1 (some (.leaf 2)) none : OptTree 0)
#guard !(OptTree.node 1 (some (.leaf 2)) none == (OptTree.node 1 (some (.leaf 3)) none : OptTree 0))
#guard !(OptTree.node 1 (some (.leaf 2)) none == (OptTree.node 1 none (some (.leaf 2)) : OptTree 0))

end TestI9

-- ============================================================
-- Test I10: Indexed mutual pair (two indexed types, same index,
-- referencing each other)
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting, just mutual)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI10

mutual
inductive Stmt : Nat → Type where
  | skip : Stmt n
  | assign : String → Expr n → Stmt n
inductive Expr : Nat → Type where
  | lit : Nat → Expr n
  | var : String → Expr n
end

derive_deceq Stmt

#guard Stmt.skip == (Stmt.skip : Stmt 0)
#guard Stmt.assign "x" (.lit 1) == (Stmt.assign "x" (.lit 1) : Stmt 0)
#guard !(Stmt.assign "x" (.lit 1) == (Stmt.assign "y" (.lit 1) : Stmt 0))
#guard !(Stmt.assign "x" (.lit 1) == (Stmt.assign "x" (.var "y") : Stmt 0))
#guard Expr.lit 42 == (Expr.lit 42 : Expr 5)
#guard !(Expr.lit 42 == (Expr.var "x" : Expr 5))

end TestI10

-- ============================================================
-- Test I11: Three-index family
--
-- deriving BEq:          ✓
-- deriving DecidableEq:  ✓ (no nesting)
-- derive_deceq:          ✓
-- ============================================================
namespace TestI11

inductive Tensor : Nat → Nat → Nat → Type where
  | scalar : Nat → Tensor 0 0 0
  | vec : Nat → Tensor a b c → Tensor a b (c + 1)

derive_deceq Tensor

#guard Tensor.scalar 5 == Tensor.scalar 5
#guard !(Tensor.scalar 5 == Tensor.scalar 6)
#guard Tensor.vec 1 (.scalar 2) == Tensor.vec 1 (.scalar 2)
#guard !(Tensor.vec 1 (.scalar 2) == Tensor.vec 1 (.scalar 3))
#guard !(Tensor.vec 1 (.scalar 2) == Tensor.vec 2 (.scalar 2))

end TestI11

-- ============================================================
-- Test I12: Kitchen-sink stress test
-- Packs as many features as possible into one mutual block:
--   • parametric (α)
--   • mutual (Cmd/Fun reference each other)
--   • nested via custom container (MyList, not stdlib List)
--   • nested via stdlib List
--   • nested via Option
--   • nested via double Option (Option (Option _))
--   • Prop-typed field (Fun.ext)
--   • direct recursion (Cmd.seq)
--   • non-recursive constructors (Cmd.ret, Fun.ext)
--
-- Container nesting + genuine index-changing recursion is
-- incompatible at the kernel level (nested inductive parameters
-- cannot contain local variables), so indices are omitted here.
-- Index-changing recursion is exercised separately in Test I7.
--
-- derive_deceq:          ✓
-- ============================================================
namespace TestI12

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
  deriving DecidableEq

axiom Invariant : Nat → Prop

mutual
inductive Cmd (α : Type) where
  | ret : α → Cmd α                                        -- parametric leaf
  | seq : Cmd α → Cmd α → Cmd α                            -- direct recursion
  | many : MyList (Cmd α) → Cmd α                          -- custom container nesting
  | invoke : Fun α → Cmd α                                 -- mutual reference
inductive Fun (α : Type) where
  | defn : α → Cmd α → Fun α                               -- mutual + parametric
  | ext : α → Invariant 0 → Fun α                          -- Prop-typed field
  | over : List (Fun α) → Option (Fun α) → Fun α           -- List + Option nesting
  | wrap : Option (Option (Fun α)) → Fun α                 -- double Option nesting
end

derive_deceq Cmd

-- Cmd: basic
#guard Cmd.ret 1 == Cmd.ret 1
#guard !(Cmd.ret 1 == Cmd.ret 2)
#guard Cmd.seq (.ret 1) (.ret 2) == Cmd.seq (.ret 1) (.ret 2)
#guard !(Cmd.seq (.ret 1) (.ret 2) == Cmd.seq (.ret 1) (.ret 3))

-- Cmd: custom container (MyList)
#guard Cmd.many (.cons (.ret 1) .nil) == Cmd.many (.cons (.ret 1) .nil)
#guard !(Cmd.many (.cons (.ret 1) .nil) == Cmd.many (.cons (.ret 2) .nil))
#guard !(Cmd.many .nil == Cmd.many (.cons (.ret 1) .nil))

-- Fun: basic + parametric
#guard Fun.defn 1 (.ret 2) == Fun.defn 1 (.ret 2)
#guard !(Fun.defn 1 (.ret 2) == Fun.defn 3 (.ret 2))
#guard !(Fun.defn 1 (.ret 2) == Fun.defn 1 (.ret 3))

-- Fun: List + Option nesting
#guard Fun.over [] none == (Fun.over [] none : Fun Nat)
#guard Fun.over [.defn 1 (.ret 2)] (some (.defn 3 (.ret 4)))
    == (Fun.over [.defn 1 (.ret 2)] (some (.defn 3 (.ret 4))) : Fun Nat)
#guard !(Fun.over [.defn 1 (.ret 2)] none
    == (Fun.over [.defn 1 (.ret 3)] none : Fun Nat))
#guard !(Fun.over [] (some (.defn 1 (.ret 2)))
    == (Fun.over [] none : Fun Nat))

-- Fun: double Option nesting
#guard Fun.wrap none == (Fun.wrap none : Fun Nat)
#guard Fun.wrap (some none) == (Fun.wrap (some none) : Fun Nat)
#guard Fun.wrap (some (some (.defn 1 (.ret 2))))
    == (Fun.wrap (some (some (.defn 1 (.ret 2)))) : Fun Nat)
#guard !(Fun.wrap none == (Fun.wrap (some none) : Fun Nat))
#guard !(Fun.wrap (some none)
    == (Fun.wrap (some (some (.defn 1 (.ret 2)))) : Fun Nat))

-- Cross-type deep: Cmd → Fun → Cmd (via MyList)
#guard Cmd.invoke (.defn 1 (.many (.cons (.ret 2) .nil)))
    == Cmd.invoke (.defn 1 (.many (.cons (.ret 2) .nil)))
#guard !(Cmd.invoke (.defn 1 (.many (.cons (.ret 2) .nil)))
    == Cmd.invoke (.defn 1 (.many (.cons (.ret 3) .nil))))

end TestI12

-- ============================================================
-- Test I13: Array container nesting. Array is a structure
-- wrapping List in the kernel, so nesting through Array should
-- produce auxiliary types similar to List nesting.
--
-- derive_deceq:          ✓
-- ============================================================
namespace TestI13

inductive ATree where
  | leaf : Nat → ATree
  | node : Array ATree → ATree

derive_deceq ATree

#guard ATree.leaf 1 == ATree.leaf 1
#guard !(ATree.leaf 1 == ATree.leaf 2)
#guard ATree.node #[.leaf 1, .leaf 2] == ATree.node #[.leaf 1, .leaf 2]
#guard !(ATree.node #[.leaf 1] == ATree.node #[.leaf 2])
#guard !(ATree.node #[] == ATree.node #[.leaf 1])

end TestI13

-- ============================================================
-- Prop-typed field (proof irrelevance).
-- Lean's built-in deriver skips Prop-typed fields by exploiting
-- proof irrelevance (all proofs of a Prop are equal); this
-- deriver does the same.
-- ============================================================
namespace TestPropTypedField

inductive Witness : Prop where | intro

inductive Tagged where
  | mk : Nat → Witness → Tagged

derive_deceq Tagged

def testTagged (a b : Tagged) : Bool := a == b

#guard Tagged.mk 1 .intro == Tagged.mk 1 .intro
#guard !(Tagged.mk 1 .intro == Tagged.mk 2 .intro)

end TestPropTypedField

-- ============================================================
-- Multiple Prop fields alongside non-Prop fields.
-- A single-constructor all-Prop inductive auto-becomes Prop, so
-- we use two constructors to keep the type in Type.
-- ============================================================
namespace TestMultiplePropFields

inductive P1 : Prop where | intro
inductive P2 : Prop where | intro

inductive AllProp where
  | mk1 : P1 → P2 → AllProp
  | mk2 : P1 → AllProp

derive_deceq AllProp

def testAllProp (a b : AllProp) : Bool := a == b

#guard AllProp.mk1 .intro .intro == AllProp.mk1 .intro .intro
#guard !(AllProp.mk1 .intro .intro == AllProp.mk2 .intro)

end TestMultiplePropFields

-- ============================================================
-- Mixed Prop and non-Prop fields in one constructor.
-- ============================================================
namespace TestPropAndDataFields

axiom MyInvariant : Nat → Prop

inductive Guarded where
  | mk : (n : Nat) → MyInvariant n → String → Guarded

derive_deceq Guarded

end TestPropAndDataFields

-- ============================================================
-- Single-index inductive family (Nat-indexed).
-- ============================================================
namespace TestNatIndexed

inductive IVec : Nat → Type where
  | nil : IVec 0
  | cons : Nat → IVec n → IVec (n + 1)

derive_deceq IVec

def testIVec (a b : IVec n) : Bool := a == b

#guard IVec.nil == IVec.nil
#guard IVec.cons 1 .nil == IVec.cons 1 .nil
#guard !(IVec.cons 1 .nil == IVec.cons 2 .nil)
#guard !(IVec.cons 1 (IVec.cons 2 .nil) == IVec.cons 1 (IVec.cons 3 .nil))

end TestNatIndexed

-- ============================================================
-- Bool-indexed family with multiple constructors per index.
-- ============================================================
namespace TestBoolIndexed

inductive Tagged : Bool → Type where
  | a : Nat → Tagged true
  | b : String → Tagged true
  | c : Tagged false

derive_deceq Tagged

def testTagged (a b : Tagged t) : Bool := a == b

#guard Tagged.a 1 == Tagged.a 1
#guard !(Tagged.a 1 == Tagged.a 2)
#guard !(Tagged.a 1 == Tagged.b "x")
#guard Tagged.c == Tagged.c

end TestBoolIndexed

-- ============================================================
-- Two-index family.
-- ============================================================
namespace TestTwoIndexFamily

inductive Matrix : Nat → Nat → Type where
  | empty : Matrix 0 0
  | cell : Nat → Matrix m n → Matrix m (n + 1)

derive_deceq Matrix

#guard Matrix.empty == Matrix.empty
#guard Matrix.cell 5 .empty == Matrix.cell 5 .empty
#guard !(Matrix.cell 5 .empty == Matrix.cell 6 .empty)

end TestTwoIndexFamily

-- ============================================================
-- Indexed family nesting through a container at the same index
-- (the kernel promotes the index to a parameter for the auxiliary
-- container motive).
-- ============================================================
namespace TestIndexedContainerSameIndex

inductive STree : Nat → Type where
  | leaf : Nat → STree n
  | node : List (STree n) → STree n

derive_deceq STree

def testSTree (a b : STree n) : Bool := a == b

#guard STree.leaf 1 == (STree.leaf 1 : STree 0)
#guard !(STree.leaf 1 == (STree.leaf 2 : STree 0))
#guard STree.node [STree.leaf 1, STree.leaf 2] == (STree.node [STree.leaf 1, STree.leaf 2] : STree 3)
#guard !(STree.node [STree.leaf 1] == (STree.node [STree.leaf 2] : STree 3))

end TestIndexedContainerSameIndex

-- ============================================================
-- Constructor with an explicit binder that also appears in the
-- return type, e.g. `mk : (n : Nat) → T n → Bool → T n`.
-- Both the recursive `T n` field and the trailing `Bool` must be
-- compared correctly when the index `n` is shared between the two
-- sides of the comparison.
-- ============================================================
namespace TestExplicitIndexInReturn

inductive T : Nat → Type where
  | leaf : T n
  | mk : (n : Nat) → T n → Bool → T n

derive_deceq T

def testT {n : Nat} (a b : T n) : Bool := a == b

#guard (T.leaf : T 0) == T.leaf
#guard T.mk 0 .leaf true == T.mk 0 .leaf true
#guard !(T.mk 0 .leaf true == T.mk 0 .leaf false)
#guard !(T.mk 0 .leaf true == (T.leaf : T 0))
#guard T.mk 0 (T.mk 0 .leaf true) false == T.mk 0 (T.mk 0 .leaf true) false
#guard !(T.mk 0 (T.mk 0 .leaf true) false == T.mk 0 (T.mk 0 .leaf false) false)

end TestExplicitIndexInReturn

-- ============================================================
-- Edge-shape regression tests
-- ============================================================


-- Universe-polymorphic type parameter.
namespace TestUnivPoly
universe u
inductive UTree (α : Type u) where
  | leaf : α → UTree α
  | node : List (UTree α) → UTree α
derive_deceq UTree
example (a b : UTree Nat) : Decidable (a = b) := inferInstance
end TestUnivPoly


-- Higher-order recursive argument: `DecidableEq` on a function space
-- is undecidable, so the deriver rejects this with a clear error.
namespace TestHigherOrderRecursive
inductive Wrec where
  | sup : (Nat → Wrec) → Wrec
  | leaf : Wrec
/--
error: derive_deceq: constructor TestHigherOrderRecursive.Wrec.sup has a higher-order recursive argument of type
  Nat → Wrec
DecidableEq on a function space is not decidable.
-/
#guard_msgs (whitespace := lax) in
derive_deceq Wrec
end TestHigherOrderRecursive


-- Empty inductive: no inhabitant, equality is vacuously decidable.
namespace TestEmpty
inductive Void0 : Type
derive_deceq Void0
example (a b : Void0) : Decidable (a = b) := inferInstance
end TestEmpty


-- Prop-valued inductive: every `a = b` holds by proof irrelevance.
namespace TestPropInductive
inductive MyProp : Prop where
  | a
  | b
derive_deceq MyProp
example (x y : MyProp) : Decidable (x = y) := inferInstance
end TestPropInductive


-- Nesting through a container parameterised by more than one type.
namespace TestMultiParamContainer
inductive Pair2 (α β : Type) where
  | mk : α → β → Pair2 α β
inductive E6 where
  | wrap : Pair2 E6 E6 → E6
  | tip : Nat → E6
derive_deceq E6
example (a b : E6) : Decidable (a = b) := inferInstance
end TestMultiParamContainer


-- Type parameter in `Sort u` — works as long as the user can supply
-- `DecidableEq` for the chosen instantiation.
namespace TestPropViaUniverse
universe u
inductive Boxed (p : Sort u) where
  | mk : Nat → p → Boxed p
derive_deceq Boxed
end TestPropViaUniverse


-- Single-constructor indexed family.
namespace TestSingleCtorIndexed
inductive Single : Nat → Type where
  | only : (n : Nat) → Single n
derive_deceq Single
example : Decidable ((Single.only 0 : Single 0) = Single.only 0) := inferInstance
end TestSingleCtorIndexed


-- Two fixed-explicit binders (both `m` and `n` appear in the return).
namespace TestMultipleFixedExplicit
inductive P2 : Nat → Nat → Type where
  | nil : P2 0 0
  | mk  : (m n : Nat) → P2 m n → Bool → P2 m n
derive_deceq P2
#guard (P2.mk 0 0 .nil true) == (P2.mk 0 0 .nil true)
#guard !((P2.mk 0 0 .nil true) == (P2.mk 0 0 .nil false))
end TestMultipleFixedExplicit


-- Fixed-explicit binder followed by a Prop-valued field.
namespace TestFixedExplicitProp
axiom Inv : Nat → Prop
inductive Wit : Nat → Type where
  | mk : (n : Nat) → (h : Inv n) → Bool → Wit n
derive_deceq Wit
end TestFixedExplicitProp


-- Recursive field where the index is a free implicit.
namespace TestFreeImplicitRecursive
inductive Spine : Nat → Type where
  | tip  : Spine 0
  | wrap : (s : Spine n) → Bool → Spine n
derive_deceq Spine
end TestFreeImplicitRecursive


-- Mix of fixed-explicit and free-implicit binders in one ctor.
namespace TestFixedAndFreeImplicit
inductive Mix : Nat → Type where
  | nilM : Mix 0
  | mkM  : {k : Nat} → (n : Nat) → Mix n → Mix k → Bool → Mix n
derive_deceq Mix
end TestFixedAndFreeImplicit


-- Implicit user-level field that is itself the inductive type.
-- `{child}` is a real field used by the comparison even though the
-- `unusedVariables` linter on the declaration cannot tell.
namespace TestImplicitRecursiveField
set_option linter.unusedVariables false in
inductive Bad where
  | mk : {child : Bad} → Nat → Bad
  | leaf : Bad
derive_deceq Bad
example (x y : Bad) : Decidable (x = y) := inferInstance
#guard (Bad.mk (child := Bad.leaf) 1) == Bad.mk (child := Bad.leaf) 1
#guard !((Bad.mk (child := Bad.leaf) 1) == Bad.mk (child := Bad.leaf) 2)
#guard !((Bad.mk (child := Bad.leaf) 1)
    == Bad.mk (child := Bad.mk (child := Bad.leaf) 0) 1)
end TestImplicitRecursiveField


-- Dependent sibling fields: the type of a later field refers to an
-- earlier one. Relies on the `subst`-chain comparison.
namespace TestDependentSibling
inductive DepT where
  | mk : (n : Nat) → Fin n → Fin n → DepT
derive_deceq DepT
example (a b : DepT) : Decidable (a = b) := inferInstance
#guard DepT.mk 2 ⟨0, by decide⟩ ⟨1, by decide⟩ == DepT.mk 2 ⟨0, by decide⟩ ⟨1, by decide⟩
#guard !(DepT.mk 2 ⟨0, by decide⟩ ⟨1, by decide⟩ == DepT.mk 2 ⟨1, by decide⟩ ⟨1, by decide⟩)
end TestDependentSibling


-- Mutual block where members have different index arities.
namespace TestHeterogeneousIndices
mutual
inductive Plain where
  | a
  | b : Plain → Plain
inductive Idx : Nat → Type where
  | mk   : Plain → Idx 0
  | wrap : Idx n → Idx (n+1)
end
derive_deceq Plain
#guard Plain.a == Plain.a
#guard !(Plain.a == Plain.b Plain.a)
end TestHeterogeneousIndices


-- `private` inductive: the generated `def` and instance are also
-- private, matching Lean's name mangling for the source type.
namespace TestPrivateInductive
private inductive Hidden where
  | a
  | b
derive_deceq Hidden
example (x y : Hidden) : Decidable (x = y) := inferInstance
#guard Hidden.a == Hidden.a
#guard !(Hidden.a == Hidden.b)
end TestPrivateInductive


-- Phantom type parameter (`α` appears nowhere in the ctors).
namespace TestPhantomParam
inductive Phantom (α : Type) where
  | mk : Nat → Phantom α
derive_deceq Phantom
example : DecidableEq (Phantom Nat) := inferInstance
end TestPhantomParam


-- Instantiating a parametric derived type at a container of another
-- derived type.
namespace TestContainerOfInductiveParam
inductive Bar2 where
  | b1
  | b2
inductive Foo2 (α : Type) where
  | f  : α → Foo2 α
  | nf : List (Foo2 α) → Foo2 α
derive_deceq Foo2
derive_deceq Bar2
example (a b : Foo2 (List Bar2)) : Decidable (a = b) := inferInstance
end TestContainerOfInductiveParam
