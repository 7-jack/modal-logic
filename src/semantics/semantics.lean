

import syntax.syntax
import logic.basic data.set.basic
local attribute [instance] classical.prop_decidable

open form

/- SEMANTICS -/

/-

We now want to define a *semantics* for our language.#check



-/

---------------------- Semantics ----------------------


/-

In classical modal logic, a frame is a pair F = ⟨W, R⟩
where W is a *non-empty* set of worlds and R is a 
binary relation on W (indicating which worlds are related to 
which others).

-/
structure frame :=
(W : Type)
(W_inhabited : inhabited W)
(R : W → W → Prop)


/-

Truth at a world

In modal logic, a formula A is true at a world if.

-/
def true_at_world (f : frame) (v : nat → f.W → Prop) : f.W → form → Prop
  | w (bot)    := false
  | w (var n)  := v n w
  | w (A & B)  := (true_at_world w A) ∧ (true_at_world w B)
  | w (A ⊃ B) := (true_at_world w A) → (true_at_world w B)
  | w (box A)  := ∀ y, f.R w y → true_at_world y A


/-

Now we define semantic entailment. Say we have a set of formulas Γ
a formula A. We say that Γ *entails* A iff:

For each model M = ⟨W, R, V⟩ and w ∈ W, 
*if*   M, w ⊩ B for every B ∈ Γ,
*then* M, w ⊩ A

We'll encode the *if* in its own definition 'ctx_true_in_frame'

-/

/- Given a model (specified by f and v), 
all formulas in the context are true at all worlds in the model -/

-- A context is true at a world in a model if each 
-- formula of the context is true at that world in that model
def ctx_true_in_model (f : frame) (v : nat → f.W → Prop) 
  (Γ : ctx) := ∀ A, ∀ w, A ∈ Γ → true_at_world f v w A


-- Global semantic consequence
def entails (Γ : ctx) (A : form) :=
  ∀ f v, ctx_true_in_model f v Γ → ∀ x, true_at_world f v x A

/-----------------/

/- A formula A is valid in a specific model if true at each world -/
def valid_in_model (A : form) (f : frame) 
  (v : nat → f.W → Prop) := 
  ∀ w, true_at_world f v w A


/- A formula A is valid in a specific frame if true at each model in the frame -/
def valid_in_frame (A : form) (f : frame) := 
  ∀ v w, true_at_world f v w A


/- A formula A is valid in a *class* of frames if true at each frame in the class -/
def valid_in_frame_class (A : form) (F : set (frame)) := 
  ∀ f ∈ F, ∀ v w, true_at_world f v w A


/- Finally, there are certain formulas that are universally valid -/
def valid_universally (A : form) := 
  ∀ f v w, true_at_world f v w A


lemma not_forces_imp :  ∀ f v x A, 
  (¬(true_at_world f v x A)) ↔ (true_at_world f v x (¬A)) :=
begin
intros f v x A, split, 
repeat {intros h1 h2, exact h1 h2},
end


lemma forces_exists {f : frame} {v : nat → f.W → Prop} {x : f.W} {A : form} :
  true_at_world f v x (◇A) ↔ ∃ y : f.W, (f.R x y ∧ true_at_world f v y A) :=
begin
split, intro h1,
repeat {rw true_at_world at h1},
have h2 := not_or_of_imp h1,
cases h2, push_neg at h2,
cases h2 with y h2, cases h2 with h2 h3,
existsi (y : f.W), split, exact h2,
have h4 := (not_forces_imp f v y (¬A)).mp h3,
repeat {rw true_at_world at h4}, repeat {rw imp_false at h4},
rw not_not at h4, exact h4,
exact false.elim h2,
intro h1, cases h1 with y h1,
cases h1 with h1 h2,
intro h3,
exact absurd h2 (h3 y h1)
end