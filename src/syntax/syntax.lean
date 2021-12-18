

--------------------------------------------------------------------------------
/- SYNTAX -/
--------------------------------------------------------------------------------

/-

In our aim to formalize modal logic, we first need to capture its syntax. 
To do this, we'll implement a deep embedding in Lean.

-/

--------------------------------------------------------------------------------

/- 

§ Formulas

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
in Lean similarly. Furthermore, we'll define only a select amount of these 
formulas, namely:
- '⊥' as "bot"
- sentence symbols 'pᵢ' as "var" + a natural number to identify them
- '∧' as "and", and will be denoted in Lean as "&"
- '→' as "impl" 
- '□' as "box"
The other formulas can be defined in terms of these basic ones.

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

--------------------------------------------------------------------------------

/-

§ Proof system

Here we define the proof system of K for modal logic. K is nice
because it is the smallest normal modal logic, which gives us nice features
such as completeness and soundness. The proof system itself is used to reason
about the syntax of the language: it is a set of rules about how to syntactially
"get" new formulas and make reasonings. Later on, we'll define the semantics
of modal logic which deals with meaning.

We say that there is a modal derivation (a proof in K) from a 
set of axioms (also referred to as the context) if there is a finite sequence
of formulas such that each formula B meets one of the following conditions:

1) B is an instance of a tautology

2) B is an instance of some axiom in the ctx

3) B follows by *modus ponens* of two earlier formulas 
  - i.e. both 'A' and 'A → B' occur in the ctx

4) B follows by *necessitation* of some prior formula
  - i.e. given that 'A' occurs earlier, let 
    B := □ A

-/

-- Define a context
@[reducible] def ctx : Type := set (form)
notation Γ `∪` A := set.insert A Γ

-- Proof system
inductive Kproof : ctx → form → Prop 
| ax {Γ} {A} (h : A ∈ Γ) : Kproof Γ A                               -- axiom in ctx
| pl1 {Γ} {A B}           : Kproof Γ (A ⊃ (B ⊃ A))                  -- tautologies
| pl2 {Γ} {A B C}         : Kproof Γ ((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C)))
| pl3 {Γ} {A B}           : Kproof Γ (((¬A) ⊃ (¬B)) ⊃ (((¬A) ⊃ B) ⊃ A))
| pl4 {Γ} {A B}           : Kproof Γ (A ⊃ (B ⊃ (A & B)))
| pl5 {Γ} {A B}           : Kproof Γ ((A & B) ⊃ A)
| pl6 {Γ} {A B}           : Kproof Γ ((A & B) ⊃ B)
| pl7 {Γ} {A B}           : Kproof Γ (((¬A) ⊃ (¬B)) ⊃ (B ⊃ A))
| kdist {Γ} {A B}         : Kproof Γ ((□ (A ⊃ B)) ⊃ ((□ A) ⊃ (□ B))) -- rule K 
| mp {Γ} {A B}                                                       -- modus ponens
  (hpq: Kproof Γ (A ⊃ B)) 
  (hp : Kproof Γ A)         : Kproof Γ B
| nec {Γ} {A}                                                        -- necessitation
  (hp: Kproof Γ A)          : Kproof Γ (□ A)

  /-

  Note that we hard coded some tautologies. This is because there are an 
  infinite amount of tautologies; having to prove each instance as a lemma would 
  be tedious. The following are tautologies that are hard coded:

  1) A → B → A
  2) (A → (B → C)) → ((A → B) → C)
  3) (¬A → ¬B) → ((¬A → B) → A) 
  4) A → (B → (A ∧ B))
  5) (A ∧ B) → A
  6) (A ∧ B) → B
  7) (¬A → ¬B) → (B → A)

  and an important one for modal logics, named K after Saul Kripke, 
  - □(A → B) → (□A → □B)

  -/