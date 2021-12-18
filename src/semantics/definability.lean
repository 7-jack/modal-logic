
import syntax.syntax 
import semantics.semantics
import data.set.basic
local attribute [instance] classical.prop_decidable

open form

-- Here we define the idea of definability of frames from modal logic
def defines (A : form) (F : set (frame)) := 
  ∀ f, f ∈ F ↔ valid_in_frame A f


-- In the following, we define some major, classic modal frames
variable f : frame
variables {α : Type} (r : α → α → Prop)

def euclidean       := ∀ ⦃x y z⦄, r x y → r x z → r y z 
def ref_class       : set (frame) := { f : frame | reflexive (f.R)   }
def symm_class      : set (frame) := { f : frame | symmetric (f.R)   }
def trans_class     : set (frame) := { f : frame | transitive (f.R)  }
def euclid_class    : set (frame) := { f : frame | euclidean (f.R)   }
def equiv_class     : set (frame) := { f : frame | equivalence (f.R) }
def ref_trans_class : set (frame) := ref_class ∩ trans_class
