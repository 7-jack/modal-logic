

/- SYNTΓ -/

/-

In our aim to formalize modal logic, we will aim to implement a deep embedding.
The first step in this is to formalize the syntax of modal logic in lean.

We will aim to define formulas reflecting the classical definition i.e. 

1. '⊥' is an (atomic) formula
2. '⊤' is an (atomic) formula
3. Every sentence symbol 'pᵢ' is a formula
4. If 'A' is a formula, so is '¬A' 
5. If 'A' and 'B' are formulas, so are:
    - 'A ∧ B'
    - 'A ∨ B'
    - 'A → B'
    - 'A ↔ B'
6. If 'A' is a formula, so are:
    - '□ A'
    - '◇ A'
7. Nothing else is a formula

This is an inductive definition, so we'll define these formulas
in Lean similarly.

Specifically, we'll encode '⊥' as 'bot' (and let '⊤' be its negation).#check

Since each sentence symbol is indexed, it will take an index argument.#check

-/

inductive form : Type
  | bot               : form
  | var  (n : nat)    : form 
  | and  (A B : form) : form
  | impl (A B : form) : form
  | box  (A : form)   : form


-- Notation
notation `⊥`:80  := form.bot
prefix `p`:80    := form.var
infix `&`:79     := form.and
infix `⊃`        := form.impl
notation `¬` A   := form.impl A form.bot
notation `⊤`:80  := ¬ form.bot
notation A `∨` B := ((¬A) ⊃ B)
notation A `↔` B := (A ⊃ B) & (B ⊃ A)
notation `□`:80  := form.box 
notation `◇`:80  := λ A, ¬(□(¬A))

---------------------- Proof System ----------------------

-- Define a context
@[reducible] def ctx : Type := set (form)
notation Γ `∪` A := set.insert A Γ


-- Proof system
inductive Kproof : ctx → form → Prop 
| ax {Γ} {A} (h : A ∈ Γ) : Kproof Γ A
| pl1 {Γ} {A B}           : Kproof Γ (A ⊃ (B ⊃ A))
| pl2 {Γ} {A B χ}         : Kproof Γ ((A ⊃ (B ⊃ χ)) ⊃ ((A ⊃ B) ⊃ (A ⊃ χ)))
| pl3 {Γ} {A B}           : Kproof Γ (((¬A) ⊃ (¬B)) ⊃ (((¬A) ⊃ B) ⊃ A))
| pl4 {Γ} {A B}           : Kproof Γ (A ⊃ (B ⊃ (A & B)))
| pl5 {Γ} {A B}           : Kproof Γ ((A & B) ⊃ A)
| pl6 {Γ} {A B}           : Kproof Γ ((A & B) ⊃ B)
| pl7 {Γ} {A B}           : Kproof Γ (((¬A) ⊃ (¬B)) ⊃ (B ⊃ A))
| kdist {Γ} {A B}         : Kproof Γ ((□ (A ⊃ B)) ⊃ ((□ A) ⊃ (□ B)))
| mp {Γ} {A B} 
  (hpq: Kproof Γ (A ⊃ B)) 
  (hp : Kproof Γ A)         : Kproof Γ B
| nec {Γ} {A} 
  (hp: Kproof Γ A)          : Kproof Γ (□ A)