/-!
# Exam 1

DO NOT CHEAT.
-/

/-! 
## #1 Easy Functions [15 points]

Define a function, *pythag*, that takes three natural 
numbers, call them *a, b,* and *c*, and that returns
*true* if *a^2 + b^2 = c^2* and that returns *false*
otherwise.
-/

-- Define your function here

def pythag (a b c : Nat) : Bool := a*a + b*b == c*c

-- The following test cases should then pass
#eval pythag 3 4 5  -- expect true
#eval pythag 6 7 8  -- expect false

/-! 
## #2 Recursive Functions

Define a function, sum_cubes, that takes any natural
number, *n*, as an argument, and that retrns the sum
of the cubes of the natural numbers from *1* up to *n*
inclusive.
-/

-- Define your function here

-- def sum_cubes {n : Nat} : Nat → Nat
-- |0 => 0
-- |n + 1 => (n + 1)*(n+1)*(n+1) + (sum_cubes n)

def sum_cubes : Nat → Nat
|0 => 0
|n' + 1 => (n' + 1)^3 + sum_cubes n'

-- test case: sum_cubes 4 = 1 + 8 + 27 + 64 = 100
#eval sum_cubes 4   -- expect 100


/-!
## #3 Product and Sum Types

Define two functions, called *prod_ors_to_or_prods*, 
and *or_prods_to_prod_ors* that shows that a product 
of sums be converted into a sum of products in a way
that the result can then be converted back into the
original product of sums. 

As a concrete example, you might want to show that if 
you have an apple or an orange and you have a cup or
a bowl, then you have an apple and a cup or an apple
and a bowl or an orange and a cup or an orange and a
bowl. 

Hints: 1. Be sure you understand the reasoning before
you try to define your functions. 2. Use four cases. 3. 
Use type-guided, top-down programming, assisted by the
Lean prover to work out a solution for each case.  
-/

def prod_ors_to_or_prods {α β γ δ: Type} :
  (α ⊕ β) × (γ ⊕ δ) → α × γ ⊕ α × δ ⊕ β × γ ⊕ β × δ 
|((Sum.inl a, Sum.inl c)) => Sum.inl (a,c)
|((Sum.inl a, Sum.inr d)) => Sum.inr (Sum.inl (a,d))
|(Sum.inr b, Sum.inl c) => Sum.inr (Sum.inr (Sum.inl (b,c)))
|(Sum.inr b, Sum.inr d) => Sum.inr (Sum.inr (Sum.inr (b,d)))

-- Write the second function here from scratch

def or_prods_to_prod_ors {α β γ δ : Type} :
  α × γ ⊕ α × δ ⊕ β × γ ⊕ β × δ → (α ⊕ β) × (γ ⊕ δ)
|Sum.inl (a,c) => (Sum.inl a, Sum.inl c)
|Sum.inr (Sum.inl (a,d)) => (Sum.inl a, Sum.inr d)
|Sum.inr (Sum.inr (Sum.inl (b,c))) => (Sum.inr b, Sum.inl c)
|Sum.inr (Sum.inr (Sum.inr (b,d))) => (Sum.inr b, Sum.inr d)

/-!
## #4 Propositional Logic Syntax and Semantics

Extend your Homework #7 solution to implement the
propositional logic *iff/equivalence* (↔) operator.
Note that Lean does not natively define the *iff*
Boolean operator. 
-/

-- def iff: Bool → Bool → Bool
-- |false, true => false
-- |true, false => false
-- |true, true => true
-- |false, false => true

/-!
Using our syntax for propositional logic, and the
variable names *A, O, C,* and *B*, respectively for
the propositions *I have an apple, I have an orange,
I have a cup,* and *I have a bowl* write a proposition
that having an orange or an apple and a bowl or a cup
is equivalent to having an apple and a bowl or an
apple and a cup or an orange and a bowl or an orange
and a cup.


Note: There's no need here to use our implementation
of propositional logic. Just write the expression 
here using the notation we've defined.
-/

structure var : Type :=  (n: Nat)
inductive unary_op : Type | not
inductive binary_op : Type
| and
| or
| imp
| iff
inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)
notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true
def biimplies : Bool → Bool → Bool
|true, true => true
|false, false => true
|_, _ => false
def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
| binary_op.iff => biimplies
def Interp := var → Bool  
def eval_expr : Expr → Interp → Bool 
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)

/- answer below -/

def v₀ := var.mk 0
def v₁ := var.mk 1
def v₂ := var.mk 2

def A := {var.mk 3}
def O := {var.mk 4}
def C := {var.mk 5}
def B := {var.mk 6}

def my_prop := (O ∨ A) ∧ (B ∨ C) ⇔ (A ∧ B) ∨ (A ∧ C) ∨ (O ∧ B) ∨ (O ∧ C)

/-!
## #5 Propositional Logic Validity
At the end of your updated Homework #7 file, use our
validity checking function to check your expression
for validity, in the expectation that the checker will
determine that the expression is in fact valid. 
-/

