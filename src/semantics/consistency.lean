
import syntax.syntax 
import semantics.semantics syntax.syntaxlemmas
import syntax.soundness order.zorn data.set.basic
local attribute [instance] classical.prop_decidable

open  Kproof

---------------------- Consistency ----------------------


def sem_cons (AX : ctx) := ¬ entails AX ⊥ 
attribute [class] sem_cons


lemma sem_consK : sem_cons ∅ :=
begin
rw sem_cons,
rw entails, 
push_neg, 
let f : frame := 
{ W := ℕ,
  W_inhabited := ⟨0⟩,
  R := λ x y, x = y},
use f, let v := λ n x, true,
use v, let x := 42,
split, intros A y h1, 
exact false.elim h1, use x, 
rw true_at_world, trivial 
end


lemma sem_consT : sem_cons T_axioms :=
begin
rw sem_cons, rw entails,
push_neg,
let f : frame := 
{ W := ℕ,
  W_inhabited:= ⟨0⟩,
  R := λ x y, x = y},
use f, let v := λ n x, true,
use v, let x := 42,
split, intros A y h1, 
cases h1 with B h1, subst h1,
intro h1, apply h1 y,
exact rfl, use x,
rw true_at_world, trivial
end


lemma sem_consS4 : sem_cons S4_axioms :=
begin
rw sem_cons, rw entails, push_neg,
let f : frame := 
{ W := ℕ,
  W_inhabited:= ⟨0⟩,
  R := λ x y, x = y},
use f, let v := λ n x, true,
use v, let x := 42,
split, 
intros A y h1,
cases h1,
cases h1 with B h1, subst h1,
intro h1, apply h1 y,
exact rfl,
cases h1 with B h1, subst h1,
intro h1, rw true_at_world at *,
simp at *, rw true_at_world, 
simp at *, exact h1,
use x,
rw true_at_world, trivial
end


lemma sem_consS5 : sem_cons S5_axioms :=
begin
rw sem_cons, rw entails, push_neg,
let f : frame := 
{ W := ℕ,
  W_inhabited:= ⟨0⟩,
  R := λ x y, x = y},
use f, let v := λ n x, true,
use v, let x := 42,
split, 
intros A y h1,
cases h1,
cases h1 with B h1, subst h1,
intro h1, apply h1 y,
exact rfl,
cases h1 with B h1, subst h1,
intro h1, rw true_at_world at *,
simp at *, rw true_at_world, 
exact h1, use x,
rw true_at_world, trivial
end


-- Any axiom system that is consistent does not prove false
lemma nprfalse (AX : ctx) (hax : sem_cons AX) : ¬  Kproof AX ⊥ :=
begin
have h1 : ¬ entails AX ⊥ → ¬  Kproof AX ⊥, 
{have h2 :  Kproof AX ⊥ → entails AX ⊥, from soundness AX ⊥, 
rw ←not_imp_not at h2, exact h2},
apply h1, exact hax
end


lemma prnot_to_notpr (A : form) (AX : ctx) (hax : sem_cons AX) : 
   Kproof AX (¬A) → ¬  Kproof AX A :=
begin
intro h1, by_contradiction h2,
exact absurd (mp (mp pl5 contra_equiv_false) (mp (mp pl4 h2) h1)) (nprfalse AX hax)
end 


lemma pr_to_notprnot (A : form) (AX : ctx) (hax : sem_cons AX) : 
   Kproof AX A → ¬  Kproof AX (¬A) :=
begin
have h1 := prnot_to_notpr A AX hax,
rw ←not_imp_not at h1, intro h2, apply h1, rw not_not, exact h2,
end 


-- Finite conjunction of formulas
def fin_conj : list form → form
  | []      := ⊤
  | (A::As) := A & (fin_conj As)


-- A few helper lemmas about finite conjunctions
lemma fin_conj_simp {Γ : ctx} : ∀ B : form,  Kproof Γ (¬fin_conj [B, ¬B]) :=
begin
intro B,
exact (not_and_subst phi_and_true).mpr not_contra
end


lemma imp_conj_imp_imp {Γ : ctx} {A B χ : form} {L : list form} : 
   Kproof Γ ((fin_conj (A::L)) ⊃ B) ↔  Kproof Γ (fin_conj L ⊃ (A ⊃ B)) :=
begin
split, 
intro h, dsimp [fin_conj] at h, rw and_right_imp at h, exact h,
intro h, dsimp [fin_conj], rw and_right_imp, exact h
end


lemma fin_conj_cons_imp {Γ : ctx} {A b : form} {L : list form} : 
  Kproof Γ (fin_conj (A::L) ⊃ (A ⊃ b)) →  Kproof Γ (fin_conj L ⊃ (A ⊃ b)) :=
begin
intro h, rw imp_conj_imp_imp at h, rw imp_imp_iff_imp at h, exact h, exact A,
end


lemma fin_conj_append {Γ : ctx} {L L' : list form} :
   Kproof Γ ((fin_conj L' & fin_conj L) ↔ (fin_conj (L' ++ L))) :=
begin
induction L', rw fin_conj,
exact (mp (mp pl4 (cut (mp pl6 and_switch) (mp pl5 phi_and_true))) 
  (cut (mp pl6 phi_and_true) (mp pl5 and_switch))),
exact mp (mp pl4 (cut (mp pl5 and_commute) (imp_and_imp (mp pl5 L'_ih)))) 
  (cut iden (cut (imp_and_imp (mp pl6 L'_ih)) (mp pl6 and_commute)))
end 


lemma fin_conj_empty {AX : ctx} {L : list form} (hax : sem_cons AX) :
  L = [] → ¬  Kproof AX (fin_conj L ⊃ ⊥) :=
begin
intro h1, subst h1,
by_contradiction h2,
exact absurd (mp h2 iden) (nprfalse AX hax)
end 


lemma fin_conj_repeat_helper {AX : ctx} {θ : form} {L : list form} (hax : sem_cons AX) :
  (∀ B ∈ L, B = θ) →  Kproof AX (θ ⊃ fin_conj L) :=
begin
intros h1, induction L,
exact mp pl1 iden,
simp at *,
cases h1 with h1 h2,
subst h1,
exact cut (mp double_imp pl4) (imp_and_and_imp (mp (mp pl4 iden) (L_ih h2))),
end


lemma fin_conj_repeat {AX : ctx} {A : form} {L : list form} (hax : sem_cons AX) :
  (∀ B ∈ L, B = ¬A) →  Kproof AX (¬fin_conj L) →  Kproof AX A :=
begin
intros h1 h2, induction L,
exact absurd (mp dne h2) (nprfalse AX hax),
simp at *,
cases h1 with h1 h3, 
have h5 := contrapos.mpr (fin_conj_repeat_helper hax h3),
subst h1,
exact (mp (mp pl3 (contrapos.mpr (cut h5 dne))) 
  (contrapos.mpr (cut ((demorgans.mp) (mp (mp pl6 (iff_not and_switch)) h2)) dne)))
end


lemma fin_conj_box2 {AX : ctx} {A B : form} :  Kproof AX ((□A & □B) ⊃ □(A & B)) :=
begin
exact (mp double_imp (cut2 pl6 (cut pl5 (cut (mp kdist (nec pl4)) kdist))))
end


lemma fin_conj_boxn {AX : ctx} {L : list form} : 
   Kproof AX ((fin_conj (list.map □ L)) ⊃ (□(fin_conj L))) :=
begin
induction L,
exact (mp pl1 (nec prtrue)),
exact (cut (imp_and_imp L_ih) fin_conj_box2)
end


lemma listempty {Γ : ctx} {L : list form} :
  (∀ A ∈ L, A ∈ Γ) → Γ = ∅ → L = [] := 
begin
intros h1 h2,
by_contradiction h3,
have h4 := list.length_pos_of_ne_nil,
have h5 := list.exists_mem_of_length_pos,
cases h5 (h4 h3) with A h5,
exact absurd (h1 A h5) (set.eq_empty_iff_forall_not_mem.mp h2 A)
end


-- Consistency for a finite set of formulas L
def fin_ax_consist (AX : ctx) (L : list form) := ¬  Kproof AX (fin_conj L ⊃ ⊥)


-- Consistency for an arbitrary set of formulas Γ
def ax_consist (AX Γ : ctx) :=
  ∀ L : list form, (∀ B ∈ L, B ∈ Γ) → fin_ax_consist AX L


-- Γ is maximally ax-consistent
def max_ax_consist (AX Γ : ctx) := 
  ax_consist AX Γ ∧ (∀ Γ', Γ ⊂ Γ' → ¬ ax_consist AX Γ')


lemma max_imp_ax {AX Γ : ctx} : max_ax_consist AX Γ → ax_consist AX Γ :=
begin
intro h1, exact h1.left
end


-- Lemma 5 from class notes
lemma five_helper (AX : ctx) : 
  ∀ Γ : ctx, ∀ A : form, ∀ L : list form, ∀ b : form, 
  (∀ B ∈ L, B ∈ Γ ∨ B = A) →  Kproof AX (fin_conj L ⊃ b) → ∃ L',
  (∀ B ∈ L', B ∈ Γ) ∧  Kproof AX (fin_conj L' ⊃ (A ⊃ b)) :=
begin
intros Γ A L b h1 h2, 
revert b, 
induction L,
{intros b h2, existsi ([] : list form), split, 
intros B h3, exfalso, apply list.not_mem_nil B h3, 
exact imp_if_imp_imp h2},
{intros b h2,
have h1a : ∀ (B : form), B ∈ L_tl → B ∈ Γ ∨ B = A, 
{intros B h2, apply h1 B (list.mem_cons_of_mem L_hd h2)},
have h1b : L_hd ∈ Γ ∨ L_hd = A, 
{apply h1 L_hd, left, refl},
cases h1b, 
have h3 := and_right_imp.mp h2,
cases L_ih h1a (L_hd ⊃ b) h3 with L' ih, existsi (L_hd::L' : list form),
cases ih, split, intros B h4, cases h4, 
subst h4, exact h1b, 
apply ih_left B h4, rw imp_shift at ih_right,
rw ←imp_conj_imp_imp at ih_right, exact ih_right,
have h3 :  Kproof AX (fin_conj (L_hd::L_tl) ⊃ b), 
exact h2, exact b,
have h4 := and_right_imp.mp,
have h5 :  Kproof AX (fin_conj L_tl ⊃ (A ⊃ b)), 
  from eq.subst h1b (h4 h2),
cases L_ih h1a (A ⊃ b) h5 with L' ih, 
existsi (L' : list form), split, 
exact ih.left, exact imp_imp_iff_imp.mp ih.right}
end


lemma five (AX : ctx) : 
  ∀ Γ : ctx, ∀ A : form, ¬ ax_consist AX (Γ ∪ A) → ∃ L',
  (∀ B ∈ L', B ∈ Γ) ∧  Kproof AX (fin_conj L' ⊃ ¬A) :=
begin
intro Γ, intro A, intro h1, rw ax_consist at h1, 
push_neg at h1,
cases h1 with L h1,
have h2 := five_helper AX Γ A L ⊥,
cases h1,
have h3 : (∀ (B : form), B ∈ L → B ∈ Γ ∨ B = A), 
{intros B this, exact or.swap (h1_left B this)},
apply h2 h3, rw fin_ax_consist at h1_right, rw not_not at h1_right,
exact h1_right,
end


-- Lemma 6 from class notes
lemma six_helper (AX Γ : ctx) (h : ax_consist AX Γ) :
max_ax_consist AX Γ → ∀ A : form, A ∈ Γ ∨ (¬A) ∈ Γ :=
begin
intros h1 A, rw or_iff_not_and_not, by_contradiction h2,
cases h2 with h2l h2r,
cases h1 with h1l h1r,
have h2 := h1r (Γ ∪ A), have h3 := h1r (Γ ∪ ¬A),
have h4 : ¬ax_consist AX (Γ ∪ ¬A), 
{apply h3, from set.ssubset_insert h2r},
have h5 : ¬ax_consist AX (Γ ∪ A), 
{apply h2, from set.ssubset_insert h2l}, 
clear h2 h3, have h6 := five AX Γ A _, have h7 := five AX Γ (¬A) _, 
cases h6 with L' h6, cases h7 with L h7, cases h6 with h6l h6r,
cases h7 with h7l h7r,
have h8 := imp_and_and_imp (mp (mp pl4 h6r) h7r),
have h12 := cut (mp pl6 fin_conj_append) (cut h8 (mp pl5 contra_equiv_false)),
have h13 : (∀ (B : form), B ∈ L' ++ L → B ∈ Γ), 
{intros B h13, rw list.mem_append at h13, 
cases h13, exact (h6l B) h13, exact (h7l B) h13},
exact absurd h12 ((h1l (L' ++ L)) h13),
exact h4, exact h5
end


lemma six (AX Γ : ctx) (h : ax_consist AX Γ) :
max_ax_consist AX Γ ↔ ∀ A, (A ∈ Γ ∨ (¬A) ∈ Γ) ∧ ¬(A ∈ Γ ∧ (¬A) ∈ Γ) :=
begin 
simp, split, 
intro h1, intro A, 
split, exact six_helper AX Γ h h1 A,
{rw ←not_and, by_contradiction h2,
cases h2 with h2 h3,
specialize h ([A, ¬A]), simp at *,
have h4 : (∀ (B : form), B = A ∨ B = ¬A → B ∈ Γ), 
{intros B h4, cases h4, subst h4, exact h2, subst h4, exact h3},

exact absurd (fin_conj_simp A) (h h2 h3)},
intro h1, split, exact h,
intros Γ' h2,
have h3 : Γ ⊆ Γ' ∧ ¬ Γ' ⊆ Γ, from h2,
cases h3,
rw set.not_subset at h3_right,
apply (exists.elim h3_right), simp, intros B h4 h5,
specialize h1 B, cases h1,
cases h1_left,
apply absurd h1_left h5,
have h6 := set.mem_of_subset_of_mem h3_left h1_left,
rw ax_consist, 
push_neg,
existsi ([B,¬B] : list form),
simp, split, 
apply and.intro,
exact h4,
exact h6,
rw fin_ax_consist, rw not_not,
exact fin_conj_simp B,
end


-- Exercise 1 from class notes
lemma ex1help {AX Γ : ctx} {A : form} {L L' : list form} :
  (∀ B ∈ L, B ∈ Γ) →  Kproof AX (fin_conj L ⊃ A) → (∀ B ∈ L', B ∈ (insert A Γ)) 
  → ∃ L'' : list form, (∀ B ∈ L'', B ∈ Γ) ∧  Kproof AX (fin_conj L'' ⊃ fin_conj L') :=
begin
intros h1 h2 h3, induction L',
existsi ([] : list form),
split,
intros B h4, exact false.elim h4,
exact iden,
simp at *,
cases h3 with h3 h4,
cases L'_ih h4 with L'' L'_ih,
cases L'_ih with ih1 ih2,
cases h3, 
existsi (L''++L : list form),
split,
simp at *, intros B h2,
cases h2 with h2 h5,
exact ih1 B h2,
exact h1 B h5,
subst h3, 
exact (cut (mp pl6 fin_conj_append) (cut (mp pl5 and_switch) (imp_and_and_imp (mp (mp pl4 h2) ih2)))),
existsi (L'_hd::L'' : list form),
split, simp at *, split, exact h3, exact ih1,
exact imp_and_imp ih2
end


lemma exercise1 {AX Γ : ctx} {A : form} {L : list form} :
  max_ax_consist AX Γ → (∀ B ∈ L, B ∈ Γ) →  Kproof AX (fin_conj L ⊃ A) → A ∈ Γ :=
begin
intros h1 h2 h3, 
by_contradiction h4, 
cases h1 with h1 h5, 
specialize h5 (Γ ∪ {A}), 
simp at h5,
specialize h5 (set.ssubset_insert h4), 
rw ax_consist at h5,
push_neg at h5,
cases h5 with L' h5,
cases h5 with h5 h6,
rw fin_ax_consist at h6, 
rw not_not at h6,
have h7 := ex1help h2 h3 h5,
cases h7 with L'' h7,
cases h7 with h7 h8,
apply h1 L'' h7,
exact cut h8 h6
end


lemma max_dn (AX Γ : ctx) (h : max_ax_consist AX Γ) (A : form) :
  A ∈ Γ ↔ (¬¬A) ∈ Γ :=
begin
split, intro h1, 
have h2 : (∀ B ∈ [A], B ∈ Γ) →  Kproof AX (fin_conj [A] ⊃ (¬¬A)) → (¬¬A) ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
exact (cut (mp pl5 phi_and_true) dni), 
intro h1,
have h2 : (∀ B ∈ [¬¬A], B ∈ Γ) →  Kproof AX (fin_conj [¬¬A] ⊃ A) → A ∈ Γ, from exercise1 h,
simp at *, apply h2, exact h1,
exact (cut (mp pl5 phi_and_true) dne), 
end


lemma max_boxdn (AX Γ : ctx) (h : max_ax_consist AX Γ) (A : form) :
  (¬□A) ∈ Γ → (¬□(¬¬A)) ∈ Γ :=
begin
intro h1,
have h2 : (∀ B ∈ [(¬□A)], B ∈ Γ) →  Kproof AX (fin_conj [(¬□A)] ⊃ (¬□(¬¬A))) → (¬□(¬¬A)) ∈ Γ, 
  from exercise1 h,
simp at *, apply h2, exact h1, clear h2,
exact (cut (mp pl5 phi_and_true) (mp pl5 box_dn)), 
end


lemma max_notiff (AX Γ : ctx) (h : max_ax_consist AX Γ) (A : form) :
  A ∉ Γ ↔ (¬A) ∈ Γ :=
begin
split, intro h1,
have h2 := max_imp_ax h, 
have h3 := six_helper AX Γ h2 h,
specialize h3 A, cases h3, exact absurd h3 h1, exact h3,
intro h1,
have h2 := max_imp_ax h, 
have h3 := six AX Γ h2,
cases h3, specialize h3_mp h (¬A), simp at *,
cases h3_mp with mp1 mp2,
have h4 := max_dn AX Γ h A,
rw ←not_iff_not at h4, apply h4.mpr, exact mp2 h1
end


lemma max_imp_1 {AX Γ : ctx} {A B : form} : 
  max_ax_consist AX Γ → (A ∈ Γ → B ∈ Γ) → (A ⊃ B) ∈ Γ :=
begin
intros h1 h2, rw imp_iff_not_or at h2,
cases h2,
have h3 : (∀ χ ∈ [¬A], χ ∈ Γ) →  Kproof AX (fin_conj [¬A] ⊃ (A ⊃ B)) → (A ⊃ B) ∈ Γ, from exercise1 h1,
simp at *, apply h3, 
exact (max_notiff AX Γ h1 A).mp h2,
exact cut (mp pl5 phi_and_true) (and_right_imp.mp exfalso),
have h3 : (∀ χ ∈ [B], χ ∈ Γ) →  Kproof AX (fin_conj [B] ⊃ (A ⊃ B)) → (A ⊃ B) ∈ Γ, from exercise1 h1,
simp at *, 
apply h3, exact h2, exact (cut (mp pl5 phi_and_true) pl1),
end


lemma max_imp_2 {AX Γ : ctx} {A B : form} : 
  max_ax_consist AX Γ → (A ⊃ B) ∈ Γ → A ∈ Γ → B ∈ Γ :=
begin
intros h1 h2 h3,
have h4 : (∀ χ ∈ [A, (A ⊃ B)], χ ∈ Γ) →  Kproof AX (fin_conj [A, (A ⊃ B)] ⊃ B) → B ∈ Γ, from exercise1 h1,
simp at *, apply h4, 
exact h3,
exact h2,
exact and_right_imp.mpr (mp pl5 phi_and_true),
end


lemma max_conj_1 {AX Γ : ctx} {A B : form} : 
  max_ax_consist AX Γ → (A ∈ Γ ∧ B ∈ Γ) → (A & B) ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [A], χ ∈ Γ) →  Kproof AX (fin_conj [A] ⊃ (B ⊃ (A & B))) → (B ⊃ (A & B)) ∈ Γ, 
  from exercise1 h1,
simp at *,
apply max_imp_2 h1, 
exact h3 h2.left (cut (mp pl5 phi_and_true) pl4), exact h2.right
end


lemma max_conj_2 {AX Γ : ctx} {A B : form} : 
  max_ax_consist AX Γ → (A & B) ∈ Γ → A ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(A & B)], χ ∈ Γ) →  Kproof AX (fin_conj [(A & B)] ⊃ A) → A ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2,
exact (cut (mp pl5 phi_and_true) pl5)
end


lemma max_conj_3 {AX Γ : ctx} {A B : form} : 
  max_ax_consist AX Γ → (A & B) ∈ Γ → B ∈ Γ :=
begin
intros h1 h2,
have h3 : (∀ χ ∈ [(A & B)], χ ∈ Γ) →  Kproof AX (fin_conj [(A & B)] ⊃ B) → B ∈ Γ, 
  from exercise1 h1,
simp at *, apply h3, exact h2,
exact (cut (mp pl5 phi_and_true) pl6)
end

lemma max_equiv (AX Γ : ctx) : max_ax_consist AX Γ ↔ ax_consist AX Γ ∧ 
  ∀ Γ', ax_consist AX Γ' → Γ ⊆ Γ' → Γ = Γ' :=
begin
split, 
{intro h1, split, exact h1.left, 
intros Γ' h2 h3, rw set.subset.antisymm_iff, split, exact h3,
by_contradiction h4,
exact h1.right Γ' (and.intro h3 h4) h2}, 
intro h1, split, exact h1.left,
intros Γ' h2, by_contradiction h3,
rw set.ssubset_def at h2, apply h2.right, 
rw h1.right Γ' h3 h2.left,
end


open zorn
-- Lemma: if c is a chain of sets, L is a list of elements such that 
-- every element in L is in Union(c), then there is an element m in c such that every 
-- element of L is in m.
lemma lindenhelper (c : set ctx) (h : c.nonempty) (h1 : chain (⊆) c) (L : list form) :
(∀ A ∈ L, A ∈ ⋃₀(c)) → ∃ m ∈ c, (∀ B ∈ L, B ∈ m) :=
begin
intro h2,
induction L, simp,
exact h,
have h2b : ∀ A, A ∈ L_tl → A ∈ ⋃₀(c), 
{intros A h3, apply h2, exact set.mem_union_right (eq A) h3},
cases L_ih h2b with m ih,
cases ih with h3 ih,
specialize h2 L_hd, 
simp at h2,
cases h2 with m' h2,
cases h2 with h2 h4,
existsi (m' ∪ m : ctx), 
have h5 : m' ∪ m ∈ c, 
{have h6 := chain.total_of_refl h1 h3 h2,
cases h6,
exact (eq.substr (set.union_eq_self_of_subset_right h6) h2), 
exact (eq.substr (set.union_eq_self_of_subset_left h6) h3)},
existsi (h5 : m' ∪ m ∈ c),
intros B h6, cases h6,
subst h6, exact set.mem_union_left m h4,
exact set.mem_union_right m' (ih B h6)
end


lemma lindenbaum (AX Γ : ctx) (hax : ax_consist AX Γ) : 
  ∃ Γ', max_ax_consist AX Γ' ∧ Γ ⊆ Γ' :=
begin
let P := { Γ'' | Γ'' ⊇ Γ ∧ ax_consist AX Γ''},
have h : ∀ c ⊆ P, chain (⊆) c → c.nonempty → ∃ub ∈ P, ∀ s ∈ c, s ⊆ ub, 
{intros c h2 h3 h4, use ⋃₀(c), 
have h5 := lindenhelper c h4 h3,
repeat {split}, 
cases h4 with Γ'' h4,
have h6 := set.mem_of_mem_of_subset h4 h2,
cases h6 with h6 h7,
apply set.subset_sUnion_of_subset c Γ'' h6 h4,
intros L h6,
cases h5 L h6 with m h5,
cases h5 with h7 h5,
cases (set.mem_of_mem_of_subset h7 h2) with h8 h9,
apply h9, exact h5,
intros s h7, exact set.subset_sUnion_of_mem h7},
have h1 : Γ ∈ P,
split,
exact set.subset.rfl,
exact hax,
cases zorn_subset_nonempty P h Γ h1 with Γ' h2,
cases h2 with h2 h3,
cases h3 with h3 h4,
use Γ', split, rw max_equiv, split, apply h2.2, 
intros m h5 h6, symmetry, apply h4 m, split, 
apply set.subset.trans h2.1 h6,
exact h5, exact h6, apply h2.1
end


-- Corollary 8 from class notes
lemma max_ax_exists (AX : ctx) (hax : sem_cons AX) : ∃ Γ : ctx, max_ax_consist AX Γ :=
begin
have h1 : ax_consist AX ∅,
{intro L, intro h2, rw fin_ax_consist, 
have h3 := listempty h2, have this : ∅ = ∅, refl, 
specialize h3 this, subst h3, by_contradiction h4, 
apply nprfalse AX hax, exact mp dne h4},
have h2 := lindenbaum AX ∅ h1, 
cases h2 with Γ h2, cases h2 with h2 h3, existsi (Γ : ctx), apply h2
end