import Init.Prelude
import Init.Data.List.Basic
import Mathlib.Data.Int.Range
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Data.List.Intervals
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Abel
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Data.Real.Basic
import Init.Data.Int.DivModLemmas

open Mathlib
open CategoryTheory

variable {dom cod : Type}
variable {R : Type} [instR : CommRing R]
variable {I  : Type} [instI : AddCommGroup I]
variable {N : Type} [instN : AddCommMonoid N]
variable {base : Real}
universe u v u_0 u_1 u_2 u_3 u_4

namespace Wedge

-- lowest level is -1
-- structure WedgeInt {base : Nat} where
--   ofInt (n : Int) : @WedgeInt base
--   wedge (n : Int) (h : ¬∃m, n = 2^m) : @WedgeInt base

-- abbrev WedgeNat {base : Nat} := Nat

-- def log (n : Nat) : @WedgeNat base := ↑n
-- def exp (n : Nat) : @WedgeNat base := ↑n
-- def softmax (a b : @WedgeNat base) : @WedgeNat base := ↑(↑a + ↑b)
-- def add (a b : @WedgeNat base) : @WedgeNat base := ↑(↑a * ↑b)

-- def log_eq_nat (n : Nat) : HEq n (WedgeNat.log n) := by

inductive WedgeReal where
  | theta : WedgeReal
  | ofR : Real → WedgeReal
  | bar : Real → WedgeReal

theorem wedge_induction (x : WedgeReal) : (∃y : x = ofR y) ∨

def add : WedgeReal → WedgeReal → WedgeReal
  | .theta, _ => .theta
  | _, .theta => .theta
  | .ofR a, .ofR b => .ofR (a + b)
  | .ofR a, .bar b => .bar (a + b)
  | .bar a, .ofR b => .bar (a + b)
  | .bar a, .bar b => .ofR (a + b)

def wedge : WedgeReal → WedgeReal → WedgeReal
  | .theta, _ => _
  | _, .theta => _

theorem wedge_induction (x : WedgeReal) : (∃y, x = .ofReal y) ∨ (∃y, x = )

end Wedge

structure σ_rec_rel where
  n0 : cod
  sc : cod → cod

def σ_main (r : @σ_rec_rel cod) : Nat → cod
  | .zero => r.n0
  | .succ m => r.sc (σ_main r m)

structure α_rec_rel where
  n0 : N
  incr : Nat → N

def α_main (r : @α_rec_rel N) : Nat → N
  | .zero => r.n0
  | .succ m => α_main r m + r.incr m

-- If the codomain is a group, successor recurence relations can be made into additives
def σ_to_α (r : @σ_rec_rel I) [AddGroup I] : @α_rec_rel I :=
  { n0 := r.n0
    incr := fun n => (r.sc (σ_main r n) - (σ_main r n))
  }

def α_rec_rel_add (f g : @α_rec_rel N) : @α_rec_rel N :=
  { n0 := f.n0 + g.n0,
    incr := f.incr + g.incr
  }

instance inst_α_rec_rel_add : Add (@α_rec_rel N) where
  add := α_rec_rel_add

def σ_rec_rel_nat_comp (f : @σ_rec_rel Nat) (g : @σ_rec_rel Nat) : @σ_rec_rel Nat :=
  { n0 := σ_main f g.n0,
    sc := (σ_main f) ∘ g.sc }
infixl:60 " ∘ " => fun f g => σ_rec_rel_nat_comp f g

def add_rec_rel_comp (f : @α_rec_rel Nat Nat.instAddMonoid) (g : @α_rec_rel Nat Nat.instAddMonoid) : @add_rec_rel Nat Nat.instAddMonoid :=
  { n0 := (f.main (g.n0)),
    incr := }
infixl:60 " ∘ " => fun f g => add_rec_rel_comp f g

def Δ''' (step f wrt : Int → Int) : Int → Int :=
  fun x => (f ((wrt x) + (step x)) - f (wrt x)) / step x

def Δ'' (step f : Int → Int) : Int → Int :=
  fun x => (f (x + (step x)) - f x) / step x

def Δ' (step : Int) (f : Int → Int) : Int → Int :=
  fun x => ((f (x + step)) - f x) / step

def Δ (f : Nat → I) : Nat → I :=
  fun x => (f (x.succ)) - f x

theorem Δ_α_rec_rel (f : @α_rec_rel I) : Δ (α_main f) = f.incr := by
  conv => lhs; intro x; simp [Δ]
  funext x
  simp [α_main]

def f_to_α (f : Nat → I) : @α_rec_rel I :=
  { n0 := f 0,
    incr := Δ f
  }

theorem f_eq_f_as_α (f : Nat → I) : f = (α_main <| f_to_α f) := by
  conv =>
    rhs; intro x
    rw [f_to_α]
    rw [α_main.eq_def]
    simp
  funext x
  induction x with
  | zero => simp
  | succ x' hx' =>
      simp [Δ]
      abel_nf; simp
      rw [α_main.eq_def]; simp
      rw [← hx']; simp

theorem Δ'_to_Δ'' : ∀ (f : Int → Int) (step : Nat),
    Δ' step f = Δ'' (fun _ => step) f := by
  intro x step
  conv => lhs; intro y; simp [Δ']
  conv => rhs; intro y; simp [Δ'']

theorem Δ_to_Δ' : ∀f : Int → Int, Δ f = Δ' 1 f := by
  intro x
  conv => lhs; intro y; simp [Δ]
  conv => rhs; intro y; simp [Δ']

def AUC' (L : List Nat) (f : Nat → I) : I :=
  List.sum (List.map f L)

def AUC (a b : Nat) (f : Nat → I) : I :=
  if a ≤ b
  then List.sum (List.map f (List.Ico a b))
  else -List.sum (List.map f (List.Ico b a))

theorem AUC_self (a : Nat) (f : Nat → I) : AUC a a f = 0 := by
  simp [AUC]

theorem AUC_succ (a : Nat) (f : Nat → I) : AUC a (a + 1) f = f a := by
  simp [AUC]

theorem AUC_reverse (a b : Nat) (f : Nat → I) : AUC a b f = -AUC b a f := by
  simp [AUC]
  if heq : a = b
  then simp [heq]
  else have hne : a < b ∨ b < a := by rw [← Nat.lt_or_gt]; exact heq
       cases hne with
       | inl halb => have haleb : a ≤ b := by apply Nat.le_of_lt; exact halb
                     have hnblea : ¬b ≤ a := by apply Nat.not_le_of_lt; exact halb
                     simp [haleb, hnblea]
       | inr hbla => have hnaleb : ¬a ≤ b := by apply Nat.not_le_of_lt; exact hbla
                     have hblea : b ≤ a := by apply Nat.le_of_lt; exact hbla
                     simp [hnaleb, hblea]

theorem AUC_dist_mid' (a m b: Nat) (f : Nat → I) (h1 : a ≤ m) (h2 : m ≤ b) :
    (List.map f (List.Ico a m)).sum + (List.map f (List.Ico m b)).sum = (List.map f (List.Ico a b)).sum := by
  rw [← List.sum_append]
  rw [← List.map_append]
  rw [List.Ico.append_consecutive]
  exact h1; exact h2

theorem AUC_dist_mid (a m b: Nat) (f : Nat → I) (h1 : a ≤ m) (h2 : m ≤ b) :
    AUC a m f + AUC m b f = AUC a b f := by
  simp [AUC, h1, h2]
  rw [← List.sum_append]
  rw [← List.map_append]
  rw [List.Ico.append_consecutive]
  have h3 : a ≤ b := by simp [Nat.le_trans h1 h2]
  conv => rhs; simp [h3]
  exact h1; exact h2

theorem fundamental_theorem (a b : Nat) (f : Nat → I) : ∀m, AUC a b f = AUC a m f + AUC m b f := by
  intro m
  have haleboblea : a ≤ b ∨ b ≤ a := by exact Nat.le_total a b
  have halemomlea : a ≤ m ∨ m ≤ a := by exact Nat.le_total a m
  have hmleboblem : m ≤ b ∨ b ≤ m := by exact Nat.le_total m b
  match haleboblea, halemomlea, hmleboblem with
  | Or.inl haleb, Or.inl halem, Or.inl hmleb =>
    rw [AUC_dist_mid]
    exact halem; exact hmleb
  | Or.inl haleb, Or.inl halem, Or.inr hblem =>
    rw [← AUC_dist_mid a b m]
    rw [AUC_reverse m b]
    abel
    exact haleb; exact hblem
  | Or.inl haleb, Or.inr hmlea, Or.inl hmleb =>
    rw [← AUC_dist_mid m a b]
    rw [AUC_reverse a m]
    abel
    exact hmlea; exact haleb
  | Or.inl haleb, Or.inr hmlea, Or.inr hblem =>
    if haem : a = m then
    if hbem : m = b then
    have haeb : a = b := by apply Eq.trans haem hbem
    simp [haeb, haem, ← hbem]
    simp [AUC_self]; else
    have hblm : b < m := by apply Nat.lt_of_le_of_ne; exact hblem; exact hbem
    have hmleb : m ≤ b := by apply @Nat.le_trans m a b hmlea haleb
    have hnblm : ¬b < m := by apply Nat.not_lt_of_le hmleb
    absurd hblm; exact hnblm else
    have hmla : m < a := by apply Nat.lt_of_le_of_ne hmlea
    have halem : a ≤ m := by apply Nat.le_trans haleb hblem
    have hnmla : ¬m < a := by apply Nat.not_lt_of_le halem
    absurd hmla; exact hnmla
  | Or.inr hblea, Or.inl halem, Or.inl hmleb =>
    rw [AUC_dist_mid]
    exact halem; exact hmleb
  | Or.inr hblea, Or.inl halem, Or.inr hblem =>
    rw [AUC_reverse m b]
    rw [← AUC_dist_mid b a m]
    rw [AUC_reverse a b]
    abel
    exact hblea; exact halem
  | Or.inr hblea, Or.inr hmlea, Or.inl hmleb =>
    rw [AUC_reverse a m]
    rw [← AUC_dist_mid m b a]
    rw [AUC_reverse b a]
    abel
    exact hmleb; exact hblea
  | Or.inr hblea, Or.inr hmlea, Or.inr hblem =>
    sorry

-- on one hand this is completely trivial, on the other hand it's way better than taylor's theorem
theorem f_add_Δf (f : Nat → I) (n : Nat) : f n + Δ f n = f (n + 1) := by
  rw [Δ]
  abel

theorem f_add_Δf' (f : Nat → I) : f + Δ f = f ∘ (fun n => n + 1) := by
  conv => lhs; rhs; intro x; rw [Δ]
  conv => rhs; intro x
  funext x
  simp

theorem Δ_AUC {f : Nat → I} : (Δ fun b => (AUC 0 b f)) = f := by
  funext x
  rw [Δ]
  rw [fundamental_theorem 0 (x + 1) f x]
  rw [AUC_succ]
  abel

theorem AUC_Δ {f : Nat → I} : (fun x => (f 0) + AUC 0 x (Δ f)) = f := by
  funext x
  induction x with
  | zero => rw [AUC]; simp
  | succ x' hx' =>
    conv =>
      lhs; rhs;
      rw [fundamental_theorem 0 (x' + 1) (Δ f) x'];
    rw [← add_assoc]
    rw [hx']
    rw [AUC_succ]
    rw [f_add_Δf]


theorem Δ_f_mul_g [CommRing I] {f g : Nat → I} :
    Δ (f * g) = (Δ f) * g + f * (Δ g) + (Δ f) * (Δ g) := by
  conv => lhs; intro x; simp [Δ]
  conv => rhs; intro x; simp [Δ]
  funext x
  conv => congr`


theorem Δ_f_add_g {f g : Nat → I} :
    Δ (f + g) = (Δ f) + (Δ g) := by
  conv => rhs; lhs; intro x; rw [Δ]
  conv => rhs; rhs; intro x; rw [Δ]
  conv => lhs; intro x; rw [Δ]
  funext x; simp
  abel

theorem Δ_sum {f : Nat → I} {l : List (Nat → I)} : Δ l.sum = (List.map Δ l).sum := by
  conv => lhs; intro x
  conv => rhs; intro x
  funext x
  induction l with
  | nil => simp [Δ]
  | cons a as h =>
    rw [List.map]
    simp [List.sum]
    simp [Δ_f_add_g]
    rw [← List.sum]
    exact h

theorem Δ_const_mul {f : Nat → Int} {c : Int} : Δ ((Function.const Nat c) * f) = (Function.const Nat c) * Δ f := by
  conv => lhs; intro x; rw [Δ]
  conv => rhs; intro x; lhs; intro x1; rw [Δ]
  funext x
  induction c with
  | ofNat n =>
    induction n with
    | zero => simp
    | succ m hm =>
      simp
      ring1!
  | negSucc n =>
    induction n with
    | zero => simp; abel
    | succ m hm =>
      simp
      ring1!


def Δ_f_comp_g {f g : @add_rec_rel Nat Nat.instAddMonoid} : @add_rec_rel Nat Nat.instAddMonoid :=
  { n0 := f.main g.n0
    incr :=
  }

def exp : @α_rec_rel Nat :=
  { n0 := 1
    incr := id
  }

theorem Δ_exp : Δ exp.main = exp.main := by
  conv =>
    lhs; intro y
    rw [Δ, exp]; simp [Nat.repeat]
    rw [Int.two_mul]
  conv =>
    rhs; intro y
    rw [exp]; simp
  funext y
  ring1


theorem Δ_exp_f (f : Nat → Nat) : Δ (exp.main ∘ f) = (Δ (Int.ofNat ∘ f)) * (exp.main ∘ f) := by sorry


lemma test (f : Nat → I) (n : Nat) : f n + Δ f n + Δ f n + Δ (Δ f) n = f (n + 2) := by
  conv => lhs; lhs; lhs; rw [f_add_Δf]
  rw [add_assoc]
  rw [f_add_Δf]
  rw [f_add_Δf]

instance inst_mul_Nat_I : HMul Nat I I where
  hMul := fun n i => (List.map (fun x => i) (List.range n)).sum

lemma test2 (f : Nat → Int) (n : Nat) : (f n) + (3 * Δ f n) + (3 * Δ (Δ f) n) + (Δ (Δ (Δ f)) n) = f (n + 3) := by
  rw [← f_add_Δf f]
  simp [← test]
  ring1!

theorem Binomial (f : Nat → Int) (n : Nat):
    f n = (List.sum <| List.map (fun k : Nat => Nat.choose n k * ((Nat.repeat Δ k f) 0)) (List.range n.succ)) := by
  induction n with
  | zero => simp [List.range_succ, Nat.repeat, one_mul]
  | succ m hm =>
    have h : Δ f m = (List.map (fun k ↦ ↑(m.choose k) * Nat.repeat Δ (k + 1) f 0) (List.range m.succ)).sum := by
      congr!; simp
    simp
    sorry








-- theorem name2 {g f : @rec_rel Nat} {n : Nat} :
  --   ((g ∘ f).main n) = (Nat.repeat (g.main ∘ f.sc) n (g.main f.n0)) := by
  -- simp [rec_rel_comp]

-- theorem Δ_f_comp_g' (f g : Int → Int) :
--     Δ (f ∘ g) / Δ g = (Δ''' (Δ g) f g) := by
--   conv => lhs; intro x; simp [Δ]
--   conv => rhs; intro x; simp [Δ, Δ''', div_self]

-- theorem Δ_f_comp_g (f g : Int → Rat) (h : ∀y, Δ g y ≠ 0):
--     Δ (f ∘ g) = Δ g * (Δ''' (Δ g) f g) := by
--   conv at h => intro x; rw [Δ]
--   conv => lhs; intro x; simp [Δ]
--   conv => rhs; intro x; simp [Δ, Δ''']
--   funext x
--   have h0 : g x.succ - g x ≠ 0 := by apply h
--   rw [Int.mul_ediv_cancel']



-- structure Inj where
--   main : dom → cod
--   inj : ∀ (x y : dom), (main x) = (main y) ↔ x = y

-- def comp_inj_inj {X Y Z : Type} (f : @Inj Y Z) (g : @Inj X Y) : @Inj X Z :=
--   { main := f.main ∘ g.main,
--     inj := by intro x y
--               simp [Function.comp]
--               rw [f.inj, g.inj]}


def AUC'' (a b : Nat) (f : Nat → I) : I :=
  match a, b with
  | a = b => sorry
  | a < b => sorry


lemma range1 : List.range 1 = [0] := by rw [List.range, List.range.loop, List.range.loop]
lemma range_is_cons (x : Nat) : List.range (x.succ) = 0 :: (List.map (λy => y + 1) (List.range x)) := by
  induction x with
  | zero => simp; simp [range1]
  | succ n nh => simp [List.range_succ]
                 conv => rhs
                         rw [← List.cons_append]
                         rw [← nh]
                 simp [List.range_succ]
