

import data.set.basic semantics.semantics 
import semantics.definability syntax.syntaxlemmas
local attribute [instance] classical.prop_decidable

---------------------- Soundness ----------------------

theorem soundness (AX : ctx) (A : form) :  Kproof AX A → entails AX A :=
begin
intro h,
induction h,
{intros f v h x,
exact h h_A x h_h},
{intros f v x h2 h3 h4, exact h3}, 
{intros f v x h2 h3 h4 h5, apply h3, 
exact h5, apply h4, exact h5}, 
{intros f x v h1 h2 h3,
by_contradiction h4,
exact (h2 h4) (h3 h4)},
{intros f v x h1 h2 h3,
exact and.intro h2 h3},
{intros f v x h1 h2, exact h2.left},
{intros f v x h1 h2, exact h2.right},
{intros f v x h1 h2 h3, 
repeat {rw true_at_world at h2},
repeat {rw imp_false at h2}, 
rw not_imp_not at h2,
exact h2 h3}, 
{intros f v x h1 h2 h3 x' h4,
exact h2 x' h4 (h3 x' h4)}, 
{intros f v x h, 
exact (h_ih_hpq f v x h) (h_ih_hp f v x h)}, 
{intros f v h1 x y h2,
exact h_ih f v h1 y},
end


lemma soundnesshelper {Γ : ctx} {A : form} {C : set (frame)} : 
   Kproof Γ A → (∀ B ∈ Γ, valid_in_frame_class B C) → valid_in_frame_class A C :=
begin
intros h1 h2 f h3 v, induction h1,
{intro x, 
exact h2 h1_A h1_h f h3 v x},
{intros x h4 h5, exact h4},
{intros x h4 h5 h6, exact (h4 h6) (h5 h6)},
{intros x h3 h4, by_contradiction h5, specialize h3 h5, 
rw ←not_forces_imp at h3, exact h3 (h4 h5)},
{intros x h4 h5, exact and.intro h4 h5}, 
{intros x h4, exact h4.left}, 
{intros x h4, exact h4.right}, 
{intros x h4 h5, repeat {rw true_at_world at h4}, 
repeat {rw imp_false at h4},
rw not_imp_not at h4, exact h4 h5},
{intros x h3 h4, intros x' h5,
exact (h3 x' h5) (h4 x' h5)},
{intro x, exact h1_ih_hpq h2 x (h1_ih_hp h2 x)},
{intros x y h3, apply h1_ih, exact h2}
end


lemma inclusion_valid {C C' : set (frame)} : ∀ B, C ⊆ C' → valid_in_frame_class B C' → valid_in_frame_class B C :=
begin
intros A h1 h2 f h3 v x, 
exact h2 f (set.mem_of_subset_of_mem h1 h3) v x
end


def T_axioms  : ctx := {A : form | ∃ B, A = (□ B ⊃ B)}
def S4_axioms : ctx := T_axioms ∪ {A : form | ∃ B, A = (□ B ⊃ □ (□ B))}
def S5_axioms : ctx := T_axioms ∪ {A : form | ∃ B, A = (◇ B ⊃ □ (◇ B))}


lemma T_helper : ∀ A ∈ T_axioms, valid_in_frame_class A ref_class :=
begin
intros A h1 f h2 v x,
cases h1 with B h1, subst h1, 
apply ref_helper, exact h2
end


theorem T_soundness (A : form) :  Kproof T_axioms A → valid_in_frame_class A ref_class :=
begin
intro h, apply soundnesshelper, apply h, apply T_helper 
end


lemma S4_helper : ∀ A ∈ S4_axioms, valid_in_frame_class A ref_trans_class :=
begin
intros A h1 f h2 v x,
cases h2 with h2l h2r, 
cases h1 with h1 h3, 
{apply T_helper, exact h1, exact h2l},
{cases h3 with B h3, subst h3, 
apply trans_helper, exact h2r}
end


theorem S4_soundness (A : form) :  Kproof S4_axioms A → valid_in_frame_class A ref_trans_class :=
begin
intro h, apply soundnesshelper, apply h, apply S4_helper
end


lemma S5_helper : ∀ A ∈ S5_axioms, valid_in_frame_class A equiv_class :=
begin
intros A h1 f h2 v x,
cases h2 with h2l h2r, 
cases h2r with h2r h2rr,
cases h1 with h1 h3, 
{apply T_helper, exact h1, 
exact h2l},
{cases h3 with B h3, dsimp at h3,
subst h3, apply euclid_helper,
intros x y z h1 h2,
exact h2rr (h2r h1) h2}
end


theorem S5_soundness (A : form) :  Kproof S5_axioms A → valid_in_frame_class A equiv_class :=
begin
intro h, apply soundnesshelper, apply h, apply S5_helper
end