

import syntax.syntax 
import semantics.semantics paths
import data.set.basic
local attribute [instance] classical.prop_decidable

open form


---------------------- Frame Definability ----------------------


-- A defines F (a class of frames)
def defines (A : form) (F : set (frame)) := 
  ∀ f, f ∈ F ↔ valid_in_frame A f


---------------------- Definability Proofs ----------------------

variable f : frame
variables {α : Type} (r : α → α → Prop)

def euclidean       := ∀ ⦃x y z⦄, r x y → r x z → r y z 
def ref_class       : set (frame) := { f : frame | reflexive (f.R)   }
def symm_class      : set (frame) := { f : frame | symmetric (f.R)   }
def trans_class     : set (frame) := { f : frame | transitive (f.R)  }
def euclid_class    : set (frame) := { f : frame | euclidean (f.R)   }
def equiv_class     : set (frame) := { f : frame | equivalence (f.R) }
def ref_trans_class : set (frame) := ref_class ∩ trans_class


lemma equiv_ref_euclid (f : frame) : f ∈ equiv_class ↔ f ∈ (ref_class ∩ euclid_class) :=
begin
split,
intro h1, cases h1 with h1 h2, cases h2 with h2 h3,
split, exact h1, 
intros x y z h4 h5, exact h3 (h2 h4) h5,
intro h1, split, cases h1, exact h1_left,
split, cases h1 with h1 h2,
intros x y h3, exact h2 h3 (h1 x),
intros x y z h2 h3, cases h1 with h1 h4,
exact h4 (h4 h2 (h1 x)) h3
end


lemma ref_helper : ∀ A f, f ∈ ref_class → valid_in_frame ((box A) ⊃ A) f :=
begin
intros A f h v x h1, 
apply h1 x, apply h x
end


theorem ref_def : defines ((□ (p 0)) ⊃ (p 0)) (ref_class) :=
begin
intro f,
split,
{exact ref_helper (p 0) f},
{intros h x, let v := λ n y, n = 0 ∧ f.R x y,
specialize h v x,
simp [true_at_world, v] at h, exact h}
end


lemma symm_helper : ∀ A f, f ∈ symm_class → valid_in_frame (A ⊃ (□ (◇A))) f :=
begin
dsimp, intros A f h v x h1 y h2 h3,
by_contradiction h4,
exact ((h3 x) (h h2)) h1
end


theorem symm_def : defines ((p 0) ⊃ (□ (◇ (p 0)))) (symm_class) :=
begin
intro f, split,
{exact symm_helper (p 0) f},
{intro h1, by_contradiction h2, rw symm_class at h2,
rw set.nmem_set_of_eq at h2, rw symmetric at h2,
push_neg at h2,
cases h2 with x h2,
cases h2 with y h2,
let v := λ n x, n = 0 ∧ ¬ f.R y x,
specialize h1 v x,
simp [true_at_world, v] at h1,
apply h1 h2.right y h2.left,
intros y1 h3 h4, exact absurd h3 h4}
end


lemma trans_helper : ∀ A f, f ∈ trans_class → valid_in_frame (□ A ⊃ □ (□ A)) f :=
begin
intros A f h v x h1 y h3 z h4, 
exact (h1 z) ((h h3) h4)
end


lemma euclid_helper : ∀ A f, f ∈ euclid_class → valid_in_frame (◇ A ⊃ □ (◇ A)) f :=
begin
intros A f h v x h1 y h2 h3,
apply h1, intros z h4,
exact h3 z ((h h2) h4)
end



