import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_701

-- Bitwise identities, proved bit by bit.

theorem bAndComm (a b : ℕ) : a &&& b = b &&& a := Nat.land_comm a b

theorem bAndAssoc (a b c : ℕ) : a &&& b &&& c = a &&& (b &&& c) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem bOrComm (a b : ℕ) : a ||| b = b ||| a := Nat.lor_comm a b

theorem bAndOr (a b c : ℕ) : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem bAndSelf (a : ℕ) : a &&& a = a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases a.testBit i <;> rfl

theorem bAbsorb (a b : ℕ) : a &&& (a ||| b) = a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem bOrAbsorb (a b : ℕ) : a ||| (a &&& b) = a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem bOrAssoc (a b c : ℕ) : a ||| b ||| c = a ||| (b ||| c) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem bSubOr (a b c : ℕ) (h : a &&& (b ||| c) = b ||| c) : a &&& b = b := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun n => Nat.testBit n i) h
  simp only [Nat.testBit_land, Nat.testBit_lor] at this ⊢
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> cases hc : c.testBit i <;> simp_all


-- Search on bit masks over 14 sample inputs.

def T : ℕ := 992
def TOP : ℕ := 16383

def wideB (v : ℕ) : Bool := let w := v &&& 31; !Nat.beq (w &&& (w - 1)) 0

theorem wide_small : ∀ a < 32, ∀ b < 32, a &&& b = a → wideB a = true → wideB b = true := by
  decide

theorem and31_lt (a : ℕ) : a &&& 31 < 32 := by
  have := Nat.and_le_right (n := a) (m := 31); omega

theorem wideB_and31 (a : ℕ) : wideB (a &&& 31) = wideB a := by
  unfold wideB
  rw [bAndAssoc, bAndSelf]

theorem wide_mono {a b : ℕ} (hab : a &&& b = a) (ha : wideB a = true) : wideB b = true := by
  rw [← wideB_and31] at ha ⊢
  apply wide_small _ (and31_lt a) _ (and31_lt b) _ ha
  rw [show a &&& 31 &&& (b &&& 31) = (a &&& b) &&& (31 &&& 31) by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land]
    cases a.testBit i <;> cases b.testBit i <;> cases (31 : ℕ).testBit i <;> rfl, hab]
  rfl

def Pnext (P : ℕ → Prop) (z : ℕ) : ℕ → Prop := fun x => P x ∨ x = z ∨ ∃ b, P b ∧ x = b &&& z

def Closed (P : ℕ → Prop) : Prop := ∀ a b, P a → P b → P (a &&& b)

theorem closed_next {P : ℕ → Prop} (hc : Closed P) (z : ℕ) : Closed (Pnext P z) := by
  intro a b ha hb
  rcases ha with ha | rfl | ⟨p, hp, rfl⟩ <;> rcases hb with hb | rfl | ⟨q, hq, rfl⟩
  · exact Or.inl (hc _ _ ha hb)
  · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
  · exact Or.inr (Or.inr ⟨a &&& q, hc _ _ ha hq, by rw [bAndAssoc]⟩)
  · exact Or.inr (Or.inr ⟨b, hb, bAndComm _ _⟩)
  · exact Or.inr (Or.inl (bAndSelf _))
  · exact Or.inr (Or.inr ⟨q, hq, by
      rw [bAndComm, bAndAssoc, bAndSelf]⟩)
  · exact Or.inr (Or.inr ⟨p &&& b, hc _ _ hp hb, by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_land]
      cases p.testBit i <;> cases b.testBit i <;> cases z.testBit i <;> rfl⟩)
  · exact Or.inr (Or.inr ⟨p, hp, by rw [bAndAssoc, bAndSelf]⟩)
  · exact Or.inr (Or.inr ⟨p &&& q, hc _ _ hp hq, by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_land]
      cases p.testBit i <;> cases q.testBit i <;> cases z.testBit i <;> rfl⟩)

def Safe : ℕ → (ℕ → Prop) → Prop
  | 0, P => ¬ P T
  | 1, P => ¬ P T ∧ ∀ a b, P a → P b → ¬ P (a ||| b) → wideB (a ||| b) = true →
      ¬ Pnext P (a ||| b) T
  | k+2, P => ¬ P T ∧ ∀ a b, P a → P b → ¬ P (a ||| b) →
      (wideB (a ||| b) = true → Safe (k+1) (Pnext P (a ||| b))) ∧
      (wideB (a ||| b) = false → Safe k (Pnext P (a ||| b)))

theorem safe_excl {k : ℕ} {P : ℕ → Prop} (h : Safe k P) : ¬ P T := by
  match k with
  | 0 => exact h
  | 1 => exact h.1
  | _+2 => exact h.1

theorem safe_mono : ∀ (k : ℕ) (P : ℕ → Prop), Safe (k+1) P → Safe k P
  | 0, _, h => h.1
  | 1, _, h => ⟨h.1, fun a b ha hb hn hw => safe_excl ((h.2 a b ha hb hn).1 hw)⟩
  | k+2, _, h => ⟨h.1, fun a b ha hb hn =>
      ⟨fun hw => safe_mono (k+1) _ ((h.2 a b ha hb hn).1 hw),
       fun hw => safe_mono k _ ((h.2 a b ha hb hn).2 hw)⟩⟩

theorem safe_mono' {k j : ℕ} {P : ℕ → Prop} (hjk : j ≤ k) (h : Safe k P) : Safe j P := by
  induction k with
  | zero => rwa [Nat.le_zero.mp hjk]
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hjk with hlt | heq
    · exact ih (by omega) (safe_mono k P h)
    · rwa [heq]


-- The two-step analysis behind the fast test.

section TwoStep
variable (P : ℕ → Prop) (cs : ℕ)

def NWit : Prop := ∃ x y, P x ∧ P y ∧ (cs &&& x) ||| (cs &&& y) = T
def W3Wit : Prop := ∃ x y q, P x ∧ P y ∧ P q ∧ wideB (x ||| y ||| q) = true ∧ cs &&& (x ||| y ||| q) = T
def W1Wit (u : ℕ) : Prop := ∃ p q, P p ∧ P q ∧ wideB (p ||| q) = true ∧ u &&& T = T ∧
  (p ||| q) &&& T = T ∧ (cs &&& u) &&& (cs &&& (p ||| q)) = T

variable {P cs}

theorem nw_of {x y : ℕ} (hx : P x) (hy : P y) (h : cs &&& (x ||| y) = T) : NWit P cs :=
  ⟨x, y, hx, hy, by rw [← bAndOr]; exact h⟩

theorem key1 {c z : ℕ} (hcsT : cs &&& T = T) (hmin : cs &&& c = cs) (h : T = c &&& z) :
    cs &&& z = T := by
  calc cs &&& z = (cs &&& c) &&& z := by rw [hmin]
    _ = cs &&& (c &&& z) := bAndAssoc _ _ _
    _ = cs &&& T := by rw [← h]
    _ = T := hcsT

theorem tsub {c z : ℕ} (h : T = c &&& z) : c &&& T = T := by
  rw [h, ← bAndAssoc, bAndSelf]

theorem tsub2 {a b : ℕ} (h : cs &&& a &&& b = T) : b &&& T = T := by
  rw [← h]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases cs.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl

theorem tsub3 {a b : ℕ} (h : cs &&& a &&& b = T) : a &&& T = T := by
  rw [← h]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases cs.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl

theorem one_step (hcsT : cs &&& T = T) (hmin : ∀ c, P c → c &&& T = T → cs &&& c = cs)
    (hT : ¬ P T) {x y : ℕ} (hx : P x) (hy : P y) (h : Pnext P (x ||| y) T) : NWit P cs := by
  rcases h with h | h | ⟨p, hp, h⟩
  · exact absurd h hT
  · exact nw_of hx hy (by rw [← h]; exact hcsT)
  · exact nw_of hx hy (key1 hcsT (hmin p hp (tsub h)) h)

-- identities over plain variables
theorem idA (c p q z : ℕ) : c &&& (p &&& z ||| q &&& z) = c &&& z &&& (p ||| q) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases p.testBit i <;> cases q.testBit i <;> cases z.testBit i <;> rfl

theorem idB (p q z : ℕ) : (p &&& z ||| q &&& z) &&& (p ||| q) = p &&& z ||| q &&& z := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases p.testBit i <;> cases q.testBit i <;> cases z.testBit i <;> rfl

theorem idC (c z w : ℕ) : (c &&& z) &&& (c &&& w) = c &&& z &&& w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases c.testBit i <;> cases z.testBit i <;> cases w.testBit i <;> rfl

theorem idD (a q z : ℕ) : (a ||| q &&& z) &&& (a ||| q) = a ||| q &&& z := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases a.testBit i <;> cases q.testBit i <;> cases z.testBit i <;> rfl

theorem idE (c a q z : ℕ) : c &&& z &&& (a ||| q &&& z) = c &&& z &&& (a ||| q) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases a.testBit i <;> cases q.testBit i <;> cases z.testBit i <;> rfl

theorem idF (p b z : ℕ) : (p &&& z ||| b) &&& (p ||| b) = p &&& z ||| b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases p.testBit i <;> cases b.testBit i <;> cases z.testBit i <;> rfl

theorem idG (c p b z : ℕ) : c &&& z &&& (p &&& z ||| b) = c &&& z &&& (p ||| b) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases p.testBit i <;> cases b.testBit i <;> cases z.testBit i <;> rfl

theorem idH (c p q z : ℕ) : c &&& z &&& (p &&& z ||| q &&& z) = c &&& z &&& (p ||| q) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases p.testBit i <;> cases q.testBit i <;> cases z.testBit i <;> rfl

theorem idI (p z w : ℕ) : p &&& (p &&& z &&& w) = p &&& z &&& w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases p.testBit i <;> cases z.testBit i <;> cases w.testBit i <;> rfl

theorem idJ (p z w : ℕ) : z &&& (p &&& z &&& w) = p &&& z &&& w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases p.testBit i <;> cases z.testBit i <;> cases w.testBit i <;> rfl

theorem idK (c p z w : ℕ) : c &&& p &&& z &&& w = c &&& (p &&& z &&& w) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases c.testBit i <;> cases p.testBit i <;> cases z.testBit i <;> cases w.testBit i <;> rfl

theorem idL (c z w : ℕ) : c &&& z &&& (z ||| w) = c &&& z := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases z.testBit i <;> cases w.testBit i <;> rfl

theorem bOrSelf (a : ℕ) : a ||| a = a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_lor]
  cases a.testBit i <;> rfl

theorem two_step (hc : Closed P) (hcsT : cs &&& T = T)
    (hmin : ∀ c, P c → c &&& T = T → cs &&& c = cs)
    (hT : ¬ P T) {x y : ℕ} (hx : P x) (hy : P y) {a2 b2 : ℕ}
    (ha : Pnext P (x ||| y) a2) (hb : Pnext P (x ||| y) b2) (hw : wideB (a2 ||| b2) = true)
    (h : Pnext (Pnext P (x ||| y)) (a2 ||| b2) T) :
    NWit P cs ∨ W3Wit P cs ∨ W1Wit P cs (x ||| y) := by
  obtain ⟨z, hz⟩ : ∃ z, x ||| y = z := ⟨_, rfl⟩
  rw [hz] at ha hb h ⊢
  have hxy : cs &&& z = T → NWit P cs := fun e => nw_of hx hy (by rw [hz]; exact e)
  have shape : cs &&& (a2 ||| b2) = T ∨ (z &&& T = T ∧ cs &&& z &&& (a2 ||| b2) = T)
      ∨ NWit P cs := by
    rcases h with h | h | ⟨c, hcm, h⟩
    · exact Or.inr (Or.inr (one_step hcsT hmin hT hx hy (by rw [hz]; exact h)))
    · exact Or.inl (by rw [← h]; exact hcsT)
    · rcases hcm with hcm | hcm | ⟨p, hp, hcm⟩
      · exact Or.inl (key1 hcsT (hmin c hcm (tsub h)) h)
      · subst c
        refine Or.inr (Or.inl ⟨tsub h, ?_⟩)
        rw [bAndAssoc, ← h]; exact hcsT
      · subst c
        have hpT : p &&& T = T := by rw [h, idI]
        have hzT : z &&& T = T := by rw [h, idJ]
        refine Or.inr (Or.inl ⟨hzT, ?_⟩)
        rw [← hmin p hp hpT, idK, ← h]; exact hcsT
  rcases shape with hL | ⟨hzT, hM⟩ | hN
  · rcases ha with ha | ha | ⟨p, hp, ha⟩ <;> rcases hb with hb | hb | ⟨q, hq, hb⟩
    · exact Or.inl (nw_of ha hb hL)
    · subst b2; rw [← hz] at hL hw
      have e : x ||| y ||| a2 = a2 ||| (x ||| y) := bOrComm _ _
      exact Or.inr (Or.inl ⟨x, y, a2, hx, hy, ha, by rw [e]; exact hw, by rw [e]; exact hL⟩)
    · subst b2; rw [← hz] at hL hw
      have e : q &&& x ||| q &&& y ||| a2 = a2 ||| q &&& (x ||| y) := by
        rw [bOrComm, bAndOr]
      exact Or.inr (Or.inl ⟨q &&& x, q &&& y, a2, hc _ _ hq hx, hc _ _ hq hy, ha,
        by rw [e]; exact hw, by rw [e]; exact hL⟩)
    · subst a2; rw [← hz] at hL hw
      exact Or.inr (Or.inl ⟨x, y, b2, hx, hy, hb, hw, hL⟩)
    · subst a2 b2; exact Or.inl (hxy (by rwa [bOrSelf] at hL))
    · subst a2 b2; exact Or.inl (hxy (by rwa [bAndComm q, bOrAbsorb] at hL))
    · subst a2; rw [← hz] at hL hw
      have e : p &&& x ||| p &&& y ||| b2 = p &&& (x ||| y) ||| b2 := by rw [bAndOr]
      exact Or.inr (Or.inl ⟨p &&& x, p &&& y, b2, hc _ _ hp hx, hc _ _ hp hy, hb,
        by rw [e]; exact hw, by rw [e]; exact hL⟩)
    · subst a2 b2; exact Or.inl (hxy (by rwa [bOrComm, bAndComm p, bOrAbsorb] at hL))
    · subst a2 b2
      rw [idA] at hL
      have hw' : wideB (p ||| q) = true := wide_mono (idB p q z) hw
      exact Or.inr (Or.inr ⟨p, q, hp, hq, hw', tsub3 hL, tsub2 hL, by rw [idC]; exact hL⟩)
  · have fin : ∀ p q, P p → P q → wideB (p ||| q) = true →
        cs &&& z &&& (p ||| q) = T → NWit P cs ∨ W3Wit P cs ∨ W1Wit P cs z := by
      intro p q hp hq hwq hv
      exact Or.inr (Or.inr ⟨p, q, hp, hq, hwq, hzT, tsub2 hv, by rw [idC]; exact hv⟩)
    rcases ha with ha | ha | ⟨p, hp, ha⟩ <;> rcases hb with hb | hb | ⟨q, hq, hb⟩
    · exact fin _ _ ha hb hw hM
    · subst b2; exact Or.inl (hxy (by rwa [bOrComm, idL] at hM))
    · subst b2; exact fin a2 q ha hq (wide_mono (idD a2 q z) hw) (by rwa [idE] at hM)
    · subst a2; exact Or.inl (hxy (by rwa [idL] at hM))
    · subst a2 b2; exact Or.inl (hxy (by rwa [idL] at hM))
    · subst a2 b2; exact Or.inl (hxy (by rwa [idL] at hM))
    · subst a2; exact fin p b2 hp hb (wide_mono (idF p b2 z) hw) (by rwa [idG] at hM)
    · subst a2 b2; exact Or.inl (hxy (by rwa [bOrComm, idL] at hM))
    · subst a2 b2; exact fin p q hp hq (wide_mono (idB p q z) hw) (by rwa [idH] at hM)
  · exact Or.inl hN

end TwoStep

-- Computation: states are a list together with the bitset of the same elements.

def inS (S x : ℕ) : Bool := Nat.testBit S x

def addAll : List ℕ → List ℕ → ℕ → List ℕ × ℕ
  | [], L, S => (L, S)
  | x :: xs, L, S => if inS S x then addAll xs L S else addAll xs (x :: L) (S ||| (1 <<< x))

def mapAnd (v : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => (b &&& v) :: mapAnd v bs

def nextL (L : List ℕ) (S : ℕ) (v : ℕ) : List ℕ × ℕ :=
  if inS S v then (L, S) else addAll (v :: mapAnd v L) L S

def Inv (L : List ℕ) (S : ℕ) : Prop := ∀ x, inS S x = true ↔ x ∈ L

theorem inS_add (S x y : ℕ) : inS (S ||| (1 <<< x)) y = (inS S y || decide (y = x)) := by
  unfold inS
  rw [Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : y = x
  · subst h; simp
  · simp [h, Ne.symm h]

theorem addAll_spec : ∀ (xs L : List ℕ) (S : ℕ), Inv L S →
    Inv (addAll xs L S).1 (addAll xs L S).2 ∧ ∀ y, y ∈ (addAll xs L S).1 ↔ y ∈ L ∨ y ∈ xs
  | [], L, S, h => ⟨h, fun y => by simp [addAll]⟩
  | x :: xs, L, S, h => by
    unfold addAll
    by_cases hx : inS S x = true
    · rw [if_pos hx]
      obtain ⟨h1, h2⟩ := addAll_spec xs L S h
      refine ⟨h1, fun y => ?_⟩
      rw [h2]
      have hxL := (h x).mp hx
      constructor
      · rintro (hy | hy)
        · exact Or.inl hy
        · exact Or.inr (List.mem_cons_of_mem _ hy)
      · rintro (hy | hy)
        · exact Or.inl hy
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact Or.inl hxL
          · exact Or.inr hy
    · rw [if_neg hx]
      have hinv : Inv (x :: L) (S ||| (1 <<< x)) := by
        intro y
        rw [inS_add, Bool.or_eq_true, h, decide_eq_true_eq, List.mem_cons]
        tauto
      obtain ⟨h1, h2⟩ := addAll_spec xs (x :: L) _ hinv
      refine ⟨h1, fun y => ?_⟩
      rw [h2, List.mem_cons, List.mem_cons]
      tauto

theorem mapAnd_mem (v y : ℕ) : ∀ L : List ℕ, y ∈ mapAnd v L ↔ ∃ b, b ∈ L ∧ y = b &&& v
  | [] => by simp [mapAnd]
  | b :: bs => by
    simp only [mapAnd, List.mem_cons, mapAnd_mem v y bs]
    constructor
    · rintro (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨b, Or.inl rfl, rfl⟩
      · exact ⟨c, Or.inr hc, rfl⟩
    · rintro ⟨c, rfl | hc, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨c, hc, rfl⟩

theorem nextL_spec {L : List ℕ} {S : ℕ} (h : Inv L S) (hc : Closed (· ∈ L)) (v : ℕ) :
    Inv (nextL L S v).1 (nextL L S v).2 ∧
      ∀ y, y ∈ (nextL L S v).1 ↔ Pnext (· ∈ L) v y := by
  unfold nextL
  by_cases hv : inS S v = true
  · rw [if_pos hv]
    have hvL := (h v).mp hv
    refine ⟨h, fun y => ⟨fun hy => Or.inl hy, ?_⟩⟩
    rintro (hy | rfl | ⟨b, hb, rfl⟩)
    · exact hy
    · exact hvL
    · exact hc _ _ hb hvL
  · rw [if_neg hv]
    obtain ⟨h1, h2⟩ := addAll_spec (v :: mapAnd v L) L S h
    refine ⟨h1, fun y => ?_⟩
    rw [h2, List.mem_cons, mapAnd_mem]
    rfl

def cstar : List ℕ → ℕ → ℕ
  | [], c => c
  | x :: xs, c => cstar xs (if Nat.beq (x &&& T) T then c &&& x else c)

theorem cstar_spec {P : ℕ → Prop} (hc : Closed P) : ∀ (xs : List ℕ) (c : ℕ), P c →
    (∀ x ∈ xs, P x) → P (cstar xs c) ∧ cstar xs c &&& c = cstar xs c ∧
      (c &&& T = T → cstar xs c &&& T = T) ∧
      ∀ x ∈ xs, x &&& T = T → cstar xs c &&& x = cstar xs c
  | [], c, hpc, _ => ⟨hpc, bAndSelf c, id, by simp⟩
  | x :: xs, c, hpc, hxs => by
    have hx : P x := hxs x (by simp)
    set c' := (if Nat.beq (x &&& T) T then c &&& x else c) with hc'
    have hpc' : P c' := by
      rw [hc']; split
      · exact hc _ _ hpc hx
      · exact hpc
    obtain ⟨r1, r2, r3, r4⟩ := cstar_spec hc xs c' hpc' (fun y hy => hxs y (by simp [hy]))
    simp only [cstar]
    rw [← hc']
    have hc'c : c' &&& c = c' := by
      rw [hc']; split
      · rw [bAndAssoc, bAndComm x c, ← bAndAssoc, bAndSelf]
      · exact bAndSelf c
    refine ⟨r1, by rw [← r2, bAndAssoc, hc'c], ?_, ?_⟩
    · intro hcT
      apply r3
      rw [hc']; split
      · rename_i hb
        have hxT : x &&& T = T := by simpa using hb
        rw [bAndAssoc, hxT, hcT]
      · exact hcT
    · intro y hy hyT
      rcases List.mem_cons.mp hy with rfl | hy
      · have hb : Nat.beq (y &&& T) T = true := by simpa using hyT
        have hc'x : c' &&& y = c' := by
          rw [hc', if_pos hb, bAndAssoc, bAndSelf]
        rw [← r2, bAndAssoc, hc'x]
      · exact r4 y hy hyT

def optRow (S a : ℕ) : List ℕ → List ℕ → ℕ → List ℕ × ℕ
  | [], o, O => (o, O)
  | b :: bs, o, O =>
      if inS S (a ||| b) || inS O (a ||| b) then optRow S a bs o O
      else optRow S a bs ((a ||| b) :: o) (O ||| (1 <<< (a ||| b)))

def optAll (S : ℕ) : List ℕ → List ℕ → ℕ → List ℕ × ℕ
  | [], o, O => (o, O)
  | a :: as, o, O => optAll S as (optRow S a as o O).1 (optRow S a as o O).2

theorem optRow_spec (S a : ℕ) : ∀ (bs o : List ℕ) (O : ℕ), Inv o O →
    Inv (optRow S a bs o O).1 (optRow S a bs o O).2 ∧ (∀ z ∈ o, z ∈ (optRow S a bs o O).1) ∧
      ∀ b ∈ bs, inS S (a ||| b) = false → (a ||| b) ∈ (optRow S a bs o O).1
  | [], o, O, h => ⟨h, fun _ hz => hz, by simp⟩
  | b :: bs, o, O, h => by
    unfold optRow
    split
    · rename_i hc
      obtain ⟨h1, h2, h3⟩ := optRow_spec S a bs o O h
      refine ⟨h1, h2, fun b' hb' hS => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · rw [hS, Bool.false_or] at hc
        exact h2 _ ((h _).mp hc)
      · exact h3 b' hb' hS
    · have hinv : Inv ((a ||| b) :: o) (O ||| (1 <<< (a ||| b))) := by
        intro y
        rw [inS_add, Bool.or_eq_true, h, decide_eq_true_eq, List.mem_cons]
        tauto
      obtain ⟨h1, h2, h3⟩ := optRow_spec S a bs _ _ hinv
      refine ⟨h1, fun z hz => h2 z (List.mem_cons_of_mem _ hz), fun b' hb' hS => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h2 _ (List.mem_cons_self ..)
      · exact h3 b' hb' hS

theorem optAll_spec (S : ℕ) : ∀ (L o : List ℕ) (O : ℕ), Inv o O → (∀ a ∈ L, inS S a = true) →
    Inv (optAll S L o O).1 (optAll S L o O).2 ∧ (∀ z ∈ o, z ∈ (optAll S L o O).1) ∧
      ∀ a ∈ L, ∀ b ∈ L, inS S (a ||| b) = false → (a ||| b) ∈ (optAll S L o O).1
  | [], o, O, h, _ => ⟨h, fun _ hz => hz, by simp⟩
  | a :: as, o, O, h, hL => by
    unfold optAll
    obtain ⟨r1, r2, r3⟩ := optRow_spec S a as o O h
    obtain ⟨q1, q2, q3⟩ := optAll_spec S as _ _ r1 (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    refine ⟨q1, fun z hz => q2 z (r2 z hz), fun x hx y hy hS => ?_⟩
    rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
    · rw [hx, hy, bOrSelf, hL a (List.mem_cons_self ..)] at hS; exact absurd hS (by simp)
    · rw [hx] at hS ⊢; exact q2 _ (r3 y hy hS)
    · rw [hy, bOrComm] at hS ⊢; exact q2 _ (r3 x hx hS)
    · exact q3 x hx y hy hS

def sub (cs x : ℕ) : Bool := Nat.beq ((cs &&& x) &&& T) (cs &&& x)

def hitN (cs : ℕ) (A : List ℕ) : Bool :=
  A.any fun x => A.any fun y => Nat.beq ((cs &&& x) ||| (cs &&& y)) T

def hitW3 (cs : ℕ) (A : List ℕ) : Bool :=
  A.any fun x => A.any fun y => A.any fun q =>
    wideB (x ||| y ||| q) && Nat.beq (cs &&& (x ||| y ||| q)) T

-- accumulator: (all values, bitset), (values from wide pairs, bitset)
def uRow (cs x : ℕ) : List ℕ → (List ℕ × ℕ) × (List ℕ × ℕ) → (List ℕ × ℕ) × (List ℕ × ℕ)
  | [], acc => acc
  | y :: ys, ((ua, sa), (uw, sw)) =>
      if Nat.beq ((x ||| y) &&& T) T then
        let v := cs &&& (x ||| y)
        let A1 : List ℕ × ℕ := if inS sa v then (ua, sa) else (v :: ua, sa ||| (1 <<< v))
        let W1 : List ℕ × ℕ :=
          if wideB (x ||| y) && !inS sw v then (v :: uw, sw ||| (1 <<< v)) else (uw, sw)
        uRow cs x ys (A1, W1)
      else uRow cs x ys ((ua, sa), (uw, sw))

def uAll (cs : ℕ) : List ℕ → (List ℕ × ℕ) × (List ℕ × ℕ) → (List ℕ × ℕ) × (List ℕ × ℕ)
  | [], acc => acc
  | x :: xs, acc => uAll cs xs (uRow cs x (x :: xs) acc)

def UInv (acc : (List ℕ × ℕ) × (List ℕ × ℕ)) : Prop := Inv acc.1.1 acc.1.2 ∧ Inv acc.2.1 acc.2.2

def USub (acc acc' : (List ℕ × ℕ) × (List ℕ × ℕ)) : Prop :=
  (∀ z ∈ acc.1.1, z ∈ acc'.1.1) ∧ ∀ z ∈ acc.2.1, z ∈ acc'.2.1

def UHas (cs : ℕ) (acc : (List ℕ × ℕ) × (List ℕ × ℕ)) (u : ℕ) : Prop :=
  cs &&& u ∈ acc.1.1 ∧ (wideB u = true → cs &&& u ∈ acc.2.1)

theorem uRow_spec (cs x : ℕ) : ∀ (ys : List ℕ) (acc : (List ℕ × ℕ) × (List ℕ × ℕ)), UInv acc →
    UInv (uRow cs x ys acc) ∧ USub acc (uRow cs x ys acc) ∧
      ∀ y ∈ ys, (x ||| y) &&& T = T → UHas cs (uRow cs x ys acc) (x ||| y)
  | [], acc, h => ⟨h, ⟨fun _ hz => hz, fun _ hz => hz⟩, by simp⟩
  | y :: ys, ((ua, sa), (uw, sw)), h => by
    unfold uRow
    split
    · rename_i hb
      set v := cs &&& (x ||| y) with hv
      set A1 : List ℕ × ℕ := if inS sa v then (ua, sa) else (v :: ua, sa ||| (1 <<< v)) with hA1
      set W1 : List ℕ × ℕ :=
        if wideB (x ||| y) && !inS sw v then (v :: uw, sw ||| (1 <<< v)) else (uw, sw) with hW1
      have hA1i : Inv A1.1 A1.2 ∧ (∀ z ∈ ua, z ∈ A1.1) ∧ v ∈ A1.1 := by
        rw [hA1]; split
        · rename_i hs; exact ⟨h.1, fun _ hz => hz, (h.1 v).mp hs⟩
        · refine ⟨fun w => ?_, fun z hz => List.mem_cons_of_mem _ hz, List.mem_cons_self ..⟩
          simp only
          rw [inS_add, Bool.or_eq_true, h.1, decide_eq_true_eq, List.mem_cons]
          tauto
      have hW1i : Inv W1.1 W1.2 ∧ (∀ z ∈ uw, z ∈ W1.1) ∧ (wideB (x ||| y) = true → v ∈ W1.1) := by
        rw [hW1]; split
        · refine ⟨fun w => ?_, fun z hz => List.mem_cons_of_mem _ hz, fun _ => List.mem_cons_self ..⟩
          simp only
          rw [inS_add, Bool.or_eq_true, h.2, decide_eq_true_eq, List.mem_cons]
          tauto
        · rename_i hs
          refine ⟨h.2, fun _ hz => hz, fun hw => ?_⟩
          rw [hw, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at hs
          exact (h.2 v).mp hs
      obtain ⟨r1, ⟨r2, r2'⟩, r3⟩ := uRow_spec cs x ys (A1, W1) ⟨hA1i.1, hW1i.1⟩
      refine ⟨r1, ⟨fun z hz => r2 z (hA1i.2.1 z hz), fun z hz => r2' z (hW1i.2.1 z hz)⟩, ?_⟩
      intro y' hy' hyT
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact ⟨r2 _ hA1i.2.2, fun hw => r2' _ (hW1i.2.2 hw)⟩
      · exact r3 y' hy' hyT
    · rename_i hb
      obtain ⟨r1, r2, r3⟩ := uRow_spec cs x ys ((ua, sa), (uw, sw)) h
      refine ⟨r1, r2, fun y' hy' hyT => ?_⟩
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact absurd (by simpa using hyT) hb
      · exact r3 y' hy' hyT

theorem uAll_spec (cs : ℕ) : ∀ (L : List ℕ) (acc : (List ℕ × ℕ) × (List ℕ × ℕ)), UInv acc →
    UInv (uAll cs L acc) ∧ USub acc (uAll cs L acc) ∧
      ∀ x ∈ L, ∀ y ∈ L, (x ||| y) &&& T = T → UHas cs (uAll cs L acc) (x ||| y)
  | [], acc, h => ⟨h, ⟨fun _ hz => hz, fun _ hz => hz⟩, by simp⟩
  | x :: xs, acc, h => by
    unfold uAll
    obtain ⟨r1, r2, r3⟩ := uRow_spec cs x (x :: xs) acc h
    obtain ⟨q1, q2, q3⟩ := uAll_spec cs xs _ r1
    have lift : ∀ u, UHas cs (uRow cs x (x :: xs) acc) u → UHas cs (uAll cs xs (uRow cs x (x :: xs) acc)) u :=
      fun u hu => ⟨q2.1 _ hu.1, fun hw => q2.2 _ (hu.2 hw)⟩
    refine ⟨q1, ⟨fun z hz => q2.1 _ (r2.1 z hz), fun z hz => q2.2 _ (r2.2 z hz)⟩, ?_⟩
    intro a ha b hb hT
    rcases List.mem_cons.mp ha with ha | ha
    · rw [ha] at hT ⊢; exact lift _ (r3 b hb hT)
    · rcases List.mem_cons.mp hb with hb | hb
      · rw [hb, bOrComm] at hT ⊢; exact lift _ (r3 a (List.mem_cons_of_mem _ ha) hT)
      · exact q3 a ha b hb hT

def hitW1 (F W : List ℕ) : Bool := F.any fun a => W.any fun b => Nat.beq (a &&& b) T

def test (af : Bool) (L : List ℕ) (S : ℕ) : Bool :=
  !inS S T &&
  (!hitN (cstar L TOP) (L.filter (sub (cstar L TOP))) &&
  (!hitW3 (cstar L TOP) (L.filter (sub (cstar L TOP))) &&
  !hitW1 (if af then (uAll (cstar L TOP) L (([], 0), ([], 0))).1.1
      else (uAll (cstar L TOP) L (([], 0), ([], 0))).2.1)
    (uAll (cstar L TOP) L (([], 0), ([], 0))).2.1))

theorem idM1 (c x y q : ℕ) : (c &&& x) &&& (c &&& (x ||| y ||| q)) = c &&& x := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> cases q.testBit i <;> rfl

theorem idM2 (c x y q : ℕ) : (c &&& y) &&& (c &&& (x ||| y ||| q)) = c &&& y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> cases q.testBit i <;> rfl

theorem idM3 (c x y q : ℕ) : (c &&& q) &&& (c &&& (x ||| y ||| q)) = c &&& q := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases c.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> cases q.testBit i <;> rfl

theorem inv_nil : Inv [] 0 := by
  intro x; simp [inS]

theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  rw [h]; exact Nat.beq_refl b

theorem test_sound {af : Bool} {L : List ℕ} {S : ℕ} (hinv : Inv L S) (hc : Closed (· ∈ L))
    (htop : TOP ∈ L) (h : test af L S = true) :
    ¬ T ∈ L ∧ (∀ x y, x ∈ L → y ∈ L → ¬ Pnext (· ∈ L) (x ||| y) T) ∧
    (∀ x y, x ∈ L → y ∈ L → (af = true ∨ wideB (x ||| y) = true) →
      ∀ a2 b2, Pnext (· ∈ L) (x ||| y) a2 → Pnext (· ∈ L) (x ||| y) b2 →
        wideB (a2 ||| b2) = true → ¬ Pnext (Pnext (· ∈ L) (x ||| y)) (a2 ||| b2) T) := by
  unfold test at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h0, hN, hW3, hW1⟩ := h
  set cs := cstar L TOP with hcs
  obtain ⟨_, _, hcsT', hmin⟩ := cstar_spec hc L TOP htop (fun x hx => hx)
  have hcsT : cs &&& T = T := hcsT' (by decide)
  have hmin' : ∀ c, c ∈ L → c &&& T = T → cs &&& c = cs := fun c hc' hcT => hmin c hc' hcT
  have hT : ¬ T ∈ L := fun hm => by rw [(hinv T).mpr hm] at h0; exact absurd h0 (by simp)
  have memA : ∀ x, x ∈ L → (cs &&& x) &&& T = cs &&& x → x ∈ L.filter (sub cs) := by
    intro x hx he
    exact List.mem_filter.mpr ⟨hx, beq_of_eq he⟩
  have noN : ¬ NWit (· ∈ L) cs := by
    rintro ⟨x, y, hx, hy, he⟩
    have : hitN cs (L.filter (sub cs)) = true := by
      unfold hitN
      refine List.any_eq_true.mpr ⟨x, memA x hx (by rw [← he, bAbsorb]), ?_⟩
      exact List.any_eq_true.mpr ⟨y, memA y hy (by rw [← he, bOrComm, bAbsorb]), beq_of_eq he⟩
    rw [this] at hN; exact absurd hN (by simp)
  have noW3 : ¬ W3Wit (· ∈ L) cs := by
    rintro ⟨x, y, q, hx, hy, hq, hw, he⟩
    have : hitW3 cs (L.filter (sub cs)) = true := by
      unfold hitW3
      refine List.any_eq_true.mpr ⟨x, memA x hx (by rw [← he, idM1]), ?_⟩
      refine List.any_eq_true.mpr ⟨y, memA y hy (by rw [← he, idM2]), ?_⟩
      refine List.any_eq_true.mpr ⟨q, memA q hq (by rw [← he, idM3]), ?_⟩
      rw [hw, beq_of_eq he]; rfl
    rw [this] at hW3; exact absurd hW3 (by simp)
  obtain ⟨_, _, hU⟩ := uAll_spec cs L (([], 0), ([], 0)) ⟨inv_nil, inv_nil⟩
  have noW1 : ∀ x y, x ∈ L → y ∈ L → (af = true ∨ wideB (x ||| y) = true) →
      ¬ W1Wit (· ∈ L) cs (x ||| y) := by
    rintro x y hx hy hcond ⟨p, q, hp, hq, hwpq, huT, hpqT, he⟩
    have h1 := hU x hx y hy huT
    have h2 := hU p hp q hq hpqT
    have hF : cs &&& (x ||| y) ∈ (if af then (uAll cs L (([], 0), ([], 0))).1.1
        else (uAll cs L (([], 0), ([], 0))).2.1) := by
      split
      · exact h1.1
      · rename_i haf
        rcases hcond with hcond | hcond
        · exact absurd hcond haf
        · exact h1.2 hcond
    have : hitW1 (if af then (uAll cs L (([], 0), ([], 0))).1.1
        else (uAll cs L (([], 0), ([], 0))).2.1) (uAll cs L (([], 0), ([], 0))).2.1 = true := by
      unfold hitW1
      exact List.any_eq_true.mpr ⟨_, hF, List.any_eq_true.mpr ⟨_, h2.2 hwpq, beq_of_eq he⟩⟩
    rw [this] at hW1; exact absurd hW1 (by simp)
  refine ⟨hT, fun x y hx hy hn => noN (one_step hcsT hmin' hT hx hy hn), ?_⟩
  intro x y hx hy hcond a2 b2 ha hb hw hn
  rcases two_step hc hcsT hmin' hT hx hy ha hb hw hn with h' | h' | h'
  · exact noN h'
  · exact noW3 h'
  · exact noW1 x y hx hy hcond h'

def check : ℕ → List ℕ → ℕ → Bool
  | 0, _, S => !inS S T
  | 1, _, _ => false
  | 2, L, S => test false L S
  | 3, L, S => test true L S && (optAll S L [] 0).1.all (fun z =>
      !wideB z || test false (nextL L S z).1 (nextL L S z).2)
  | k+4, L, S => !inS S T && (optAll S L [] 0).1.all (fun z =>
      if wideB z then check (k+3) (nextL L S z).1 (nextL L S z).2
      else check (k+2) (nextL L S z).1 (nextL L S z).2)

theorem child_facts {L : List ℕ} {S : ℕ} (hinv : Inv L S) (hc : Closed (· ∈ L)) (htop : TOP ∈ L)
    (z : ℕ) : Inv (nextL L S z).1 (nextL L S z).2 ∧ Closed (· ∈ (nextL L S z).1) ∧
      TOP ∈ (nextL L S z).1 ∧ (fun y => y ∈ (nextL L S z).1) = Pnext (· ∈ L) z := by
  obtain ⟨h1, h2⟩ := nextL_spec hinv hc z
  have heq : (fun y => y ∈ (nextL L S z).1) = Pnext (· ∈ L) z := funext fun y => propext (h2 y)
  refine ⟨h1, ?_, (h2 TOP).mpr (Or.inl htop), heq⟩
  have := closed_next hc z
  rw [← heq] at this
  exact this

theorem opt_mem {L : List ℕ} {S : ℕ} (hinv : Inv L S) {a b : ℕ} (ha : a ∈ L) (hb : b ∈ L)
    (hn : ¬ (a ||| b) ∈ L) : (a ||| b) ∈ (optAll S L [] 0).1 := by
  obtain ⟨_, _, h3⟩ := optAll_spec S L [] 0 inv_nil (fun x hx => (hinv x).mpr hx)
  apply h3 a ha b hb
  cases hs : inS S (a ||| b)
  · rfl
  · exact absurd ((hinv _).mp hs) hn

theorem check_sound : ∀ (k : ℕ) (L : List ℕ) (S : ℕ), Inv L S → Closed (· ∈ L) → TOP ∈ L →
    check k L S = true → Safe k (· ∈ L)
  | 0, L, S, hinv, _, _, h => by
    simp only [check, Bool.not_eq_true'] at h
    intro hm; rw [(hinv T).mpr hm] at h; exact absurd h (by simp)
  | 1, _, _, _, _, _, h => by simp [check] at h
  | 2, L, S, hinv, hc, htop, h => by
    obtain ⟨hT, h1, h2⟩ := test_sound hinv hc htop h
    refine ⟨hT, fun a b ha hb _ => ⟨fun hw => ⟨h1 a b ha hb, ?_⟩, fun _ => h1 a b ha hb⟩⟩
    intro a2 b2 ha2 hb2 _ hw2
    exact h2 a b ha hb (Or.inr hw) a2 b2 ha2 hb2 hw2
  | 3, L, S, hinv, hc, htop, h => by
    simp only [check, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨ht, hall⟩ := h
    obtain ⟨hT, h1, h2⟩ := test_sound hinv hc htop ht
    refine ⟨hT, fun a b ha hb hn => ⟨fun hw => ?_, fun _ => ⟨h1 a b ha hb, ?_⟩⟩⟩
    · have hz := hall _ (opt_mem hinv ha hb hn)
      rw [hw, Bool.not_true, Bool.false_or] at hz
      obtain ⟨c1, c2, c3, c4⟩ := child_facts hinv hc htop (a ||| b)
      rw [← c4]
      exact check_sound 2 _ _ c1 c2 c3 hz
    · intro a2 b2 ha2 hb2 _ hw2
      exact h2 a b ha hb (Or.inl rfl) a2 b2 ha2 hb2 hw2
  | k+4, L, S, hinv, hc, htop, h => by
    simp only [check, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨h0, hall⟩ := h
    have hT : ¬ T ∈ L := fun hm => by rw [(hinv T).mpr hm] at h0; exact absurd h0 (by simp)
    refine ⟨hT, fun a b ha hb hn => ⟨fun hw => ?_, fun hw => ?_⟩⟩
    · have hz := hall _ (opt_mem hinv ha hb hn)
      rw [hw, if_pos rfl] at hz
      obtain ⟨c1, c2, c3, c4⟩ := child_facts hinv hc htop (a ||| b)
      rw [← c4]
      exact check_sound (k+3) _ _ c1 c2 c3 hz
    · have hz := hall _ (opt_mem hinv ha hb hn)
      rw [hw] at hz
      simp only [Bool.false_eq_true, if_false] at hz
      obtain ⟨c1, c2, c3, c4⟩ := child_facts hinv hc htop (a ||| b)
      rw [← c4]
      exact check_sound (k+2) _ _ c1 c2 c3 hz

-- Circuits to functions (after L-meta-597).

open PEqualNP.CircuitLowerBounds

abbrev F := (Fin 5 → Bool) → Bool

def inputs : List F := (fun _ => false) :: List.ofFn (fun i x => x i)

def cl (G : List F) (w : F) : Prop :=
  ∃ S : List F, (∀ f ∈ S, f ∈ G ++ inputs) ∧ ∀ x, w x = S.all (fun f => f x)

def single (u : Fin 5) : Fin 5 → Bool := fun i => decide (i = u)

abbrev wideF (g : F) : Prop := ∃ u v : Fin 5, u ≠ v ∧ g (single u) = true ∧ g (single v) = true

def good : List F → Prop
  | [] => True
  | g :: G => (∃ u v, cl G u ∧ cl G v ∧ ∀ x, g x = (u x || v x)) ∧ good G

def wsum : List F → ℕ
  | [] => 0
  | g :: G => wsum G + (if wideF g then 1 else 2)

theorem member {G : List F} {f : F} (h : f ∈ G ++ inputs) : cl G f :=
  ⟨[f], by simpa using h, by simp⟩

theorem cl_congr {G : List F} {u v : F} (hu : cl G u) (h : ∀ x, v x = u x) : cl G v := by
  obtain ⟨S, hs, he⟩ := hu
  exact ⟨S, hs, fun x => (h x).trans (he x)⟩

theorem cl_new (G : List F) (f : F) : cl (f :: G) f := member (by simp)

theorem cl_mono {G : List F} {f : F} (g : F) (h : cl G f) : cl (g :: G) f := by
  obtain ⟨S, hs, he⟩ := h
  exact ⟨S, fun v hv => List.mem_cons_of_mem _ (hs v hv), he⟩

theorem cl_true (G : List F) : cl G (fun _ => true) := ⟨[], by simp, by simp⟩

theorem cl_false (G : List F) : cl G (fun _ => false) := member (by simp [inputs])

theorem cl_and {G : List F} {a b : F} (ha : cl G a) (hb : cl G b) :
    cl G (fun x => a x && b x) := by
  obtain ⟨A,hA,eA⟩ := ha
  obtain ⟨B,hB,eB⟩ := hb
  exact ⟨A ++ B, fun g hg => (List.mem_append.mp hg).elim (hA g) (hB g),
    fun x => by simp [eA x, eB x]⟩

theorem gate_and (G : List F) (f : ℕ → F)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    cl G (fun x => GateOp.eval GateOp.and (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact cl_congr (cl_true G) (fun x => by simp [GateOp.eval])
  · exact cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact cl_congr (cl_and (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

theorem gate_or (G : List F) (f : ℕ → F)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, cl G u ∧ cl G v ∧
      ∀ x, GateOp.eval GateOp.or (ins.map fun i => f i x) = (u x || v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => false, fun _ => false, cl_false G, cl_false G,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

def W (gs : List Gate) (x : Fin 5 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def wf (gs : List Gate) (k : ℕ) : F :=
  fun x => (W gs x).getD k false

theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

theorem W_len (gs : List Gate) (x : Fin 5 → Bool) :
    (W gs x).length = 5 + gs.length := by
  unfold W
  rw [fold_len]
  simp

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 5 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 5 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 5 + gs.length
  · rw [if_pos hk]
    show (W (gs ++ [g]) x).getD k false = g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
    rw [W_snoc]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hl, hk]
  · rw [if_neg hk]
    show (W (gs ++ [g]) x).getD k false = (W gs x).getD k false
    rw [W_snoc]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    split
    · rfl
    · rename_i h2
      have h3 : ¬ (k - (5 + gs.length) = 0) := by omega
      have h4 : ¬ k < (W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

theorem base (k : ℕ) : cl [] (wf [] k) := by
  by_cases hk : k < 5
  · apply cl_congr (member (G := []) (f := fun x => x ⟨k,hk⟩) (by interval_cases k <;> simp [inputs]))
    intro x
    interval_cases k <;> rfl
  · apply cl_congr (cl_false [])
    intro x
    simp [wf, W, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk]

def IsWide (gs : List Gate) (j : ℕ) : Prop :=
  ∃ u v : Fin 5, u ≠ v ∧ wf gs (5 + j) (single u) = true ∧ wf gs (5 + j) (single v) = true

theorem card_step (A : Finset ℕ) (n : ℕ) (h : n ∈ A) :
    (A.filter (fun j => j < n)).card + 1 ≤ (A.filter (fun j => j < n + 1)).card := by
  have hsub : insert n (A.filter (fun j => j < n)) ⊆ A.filter (fun j => j < n + 1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_filter] at hj ⊢
    rcases hj with rfl | ⟨h1, h2⟩
    · exact ⟨h, by omega⟩
    · exact ⟨h1, by omega⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at hc
  exact hc

theorem card_mono (A : Finset ℕ) (n : ℕ) :
    (A.filter (fun j => j < n)).card ≤ (A.filter (fun j => j < n + 1)).card := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, by omega⟩

theorem invOR (B D : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.or ∨ g.op = GateOp.and) ∧ g.inputs.length ≤ 2)
    (hB : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.or → IsWide gs j → j ∈ B)
    (hD : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.or → ¬ IsWide gs j → j ∈ D) :
    ∃ G, good G ∧ wsum G ≤ (B.filter (fun j => j < gs.length)).card +
      2 * (D.filter (fun j => j < gs.length)).card ∧ ∀ k, cl G (wf gs k) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], trivial, by simp [wsum], fun k => base k⟩
  | append_singleton gs g ih =>
    have pre : ∀ j, j < gs.length → wf (gs ++ [g]) (5 + j) = wf gs (5 + j) := by
      intro j hj; rw [wf_snoc, if_neg (by omega)]
    have preW : ∀ j, j < gs.length → (IsWide (gs ++ [g]) j ↔ IsWide gs j) := by
      intro j hj; unfold IsWide; rw [pre j hj]
    have getPre : ∀ j g', gs[j]? = some g' → (gs ++ [g])[j]? = some g' ∧ j < gs.length := by
      intro j g' hj
      have hjl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
      exact ⟨by rw [List.getElem?_append_left hjl]; exact hj, hjl⟩
    obtain ⟨G, hG, hlen, hw⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
      (fun j g' hj ho hwd => by
        obtain ⟨h1, h2⟩ := getPre j g' hj
        exact hB j g' h1 ho ((preW j h2).mpr hwd))
      (fun j g' hj ho hwd => by
        obtain ⟨h1, h2⟩ := getPre j g' hj
        exact hD j g' h1 ho (fun h' => hwd ((preW j h2).mp h')))
    obtain ⟨hop, hl⟩ := hm g (by simp)
    have hlast : (gs ++ [g])[gs.length]? = some g := by simp
    have hnew : wf (gs ++ [g]) (5 + gs.length) = fun x => g.op.eval (g.inputs.map fun i => wf gs i x) := by
      rw [wf_snoc, if_pos rfl]
    have hBm := card_mono B gs.length
    have hDm := card_mono D gs.length
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at *
    rcases hop with hop | hop
    · obtain ⟨u, v, hu, hv, he⟩ := gate_or G (wf gs) hw g.inputs hl
      set gf : F := fun x => GateOp.eval GateOp.or (g.inputs.map fun i => wf gs i x) with hgf
      refine ⟨gf :: G, ⟨⟨u, v, hu, hv, he⟩, hG⟩, ?_, ?_⟩
      · have hwide : IsWide (gs ++ [g]) gs.length ↔ wideF gf := by
          unfold IsWide wideF; rw [hnew, hop]
        simp only [wsum]
        by_cases hwd : wideF gf
        · rw [if_pos hwd]
          have := card_step B gs.length (hB gs.length g hlast hop (hwide.mpr hwd))
          omega
        · rw [if_neg hwd]
          have := card_step D gs.length (hD gs.length g hlast hop (fun h' => hwd (hwide.mp h')))
          omega
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 5 + gs.length
        · rw [if_pos hk]; exact cl_new _ _
        · rw [if_neg hk]; exact cl_mono _ (hw k)
    · refine ⟨G, hG, by omega, ?_⟩
      intro k
      rw [wf_snoc, hop]
      by_cases hk : k = 5 + gs.length
      · rw [if_pos hk]; exact gate_and G (wf gs) hw g.inputs hl
      · rw [if_neg hk]; exact hw k

-- Sampling at 14 inputs.

def ptsL : List ℕ := [1, 2, 4, 8, 16, 3, 5, 6, 9, 24, 10, 12, 18, 20]

def sample (j : ℕ) : Fin 5 → Bool := fun i => Nat.testBit (ptsL.getD j 0) i

def rep (f : F) (v : ℕ) : Prop := ∀ j, Nat.testBit v j = (decide (j < 14) && f (sample j))

theorem rep_and {f g : F} {a b : ℕ} (ha : rep f a) (hb : rep g b) :
    rep (fun x => f x && g x) (a &&& b) := by
  intro j; simp only [Nat.testBit_land, ha j, hb j]
  cases decide (j < 14) <;> cases f (sample j) <;> cases g (sample j) <;> rfl

theorem rep_or {f g : F} {a b : ℕ} (ha : rep f a) (hb : rep g b) :
    rep (fun x => f x || g x) (a ||| b) := by
  intro j; simp only [Nat.testBit_lor, ha j, hb j]
  cases decide (j < 14) <;> cases f (sample j) <;> cases g (sample j) <;> rfl

theorem small_bits {v : ℕ} (hv : v < 2 ^ 14) {j : ℕ} (hj : ¬ j < 14) : Nat.testBit v j = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem rep_top : rep (fun _ => true) TOP := by
  intro j
  by_cases hj : j < 14
  · rw [show TOP = 2 ^ 14 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simp [hj]
  · rw [small_bits (by decide) hj]; simp [hj]

theorem rep_zero : rep (fun _ => false) 0 := by
  intro j; simp

def Xs : Fin 5 → ℕ := ![353, 5282, 10436, 3848, 12816]

theorem rep_input (i : Fin 5) : rep (fun x => x i) (Xs i) := by
  intro j
  by_cases hj : j < 14
  · rw [show decide (j < 14) = true by simp [hj], Bool.true_and]
    interval_cases j <;> fin_cases i <;> rfl
  · rw [small_bits (by fin_cases i <;> decide) hj]; simp [hj]

theorem sample_single (u : Fin 5) : sample u.val = single u := by
  funext i; fin_cases u <;> fin_cases i <;> rfl

theorem rep_single {g : F} {v : ℕ} (h : rep g v) (u : Fin 5) : g (single u) = Nat.testBit v u := by
  rw [h u.val, ← sample_single u]
  simp [show u.val < 14 by omega]

theorem wide_table : ∀ w < 32, (wideB w = true ↔
    ∃ u v : Fin 5, u ≠ v ∧ Nat.testBit w u = true ∧ Nat.testBit w v = true) := by
  decide

theorem wide_link {g : F} {v : ℕ} (h : rep g v) : wideF g ↔ wideB v = true := by
  rw [← wideB_and31, wide_table _ (and31_lt v)]
  have hb : ∀ u : Fin 5, Nat.testBit (v &&& 31) u = g (single u) := by
    intro u; rw [rep_single h, Nat.testBit_land]
    have : Nat.testBit 31 u.val = true := by fin_cases u <;> rfl
    rw [this, Bool.and_true]
  unfold wideF
  simp only [hb]

def edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)]

theorem target_table : ∀ j, Nat.testBit T j = (decide (j < 14) &&
    decide (∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ sample j u = true ∧ sample j v = true)) := by
  intro j
  by_cases hj : j < 14
  · rw [show decide (j < 14) = true by simp [hj], Bool.true_and]
    interval_cases j <;> decide
  · rw [small_bits (by decide) hj]; simp [hj]

def initList : List ℕ := [0, 32, 64, 128, 256, 353, 512, 1024, 2048, 3848, 4096, 5282, 8192, 10436, 12816, 16383]

theorem initList_closed : Closed (· ∈ initList) := by
  have h : initList.all (fun a => initList.all (fun b => initList.contains (a &&& b))) = true := by
    decide
  intro a b ha hb
  simp only [List.all_eq_true, List.contains_iff_mem] at h
  exact h a ha b hb

theorem cl_rep {P : ℕ → Prop} {G : List F} {w : F} (hc : Closed P) (htop : P TOP)
    (hG : ∀ f ∈ G ++ inputs, ∃ a, P a ∧ rep f a) (hw : cl G w) : ∃ a, P a ∧ rep w a := by
  obtain ⟨S, hS, he⟩ := hw
  have aux : ∀ U : List F, (∀ f ∈ U, f ∈ G ++ inputs) →
      ∃ a, P a ∧ rep (fun x => U.all (fun f => f x)) a := by
    intro U hU
    induction U with
    | nil => exact ⟨TOP, htop, by simpa using rep_top⟩
    | cons f U ih =>
      obtain ⟨a, ha, ea⟩ := hG f (hU f (by simp))
      obtain ⟨b, hb, eb⟩ := ih (fun t ht => hU t (List.mem_cons_of_mem _ ht))
      exact ⟨a &&& b, hc _ _ ha hb, by simpa [List.all_cons] using rep_and ea eb⟩
  obtain ⟨a, ha, ea⟩ := aux S hS
  exact ⟨a, ha, fun j => by rw [ea j]; congr 1; exact (he _).symm⟩

theorem safe_step {r c : ℕ} {P : ℕ → Prop} {a b : ℕ} (hs : Safe r P) (ha : P a) (hb : P b)
    (hn : ¬ P (a ||| b)) (hcost : c = if wideB (a ||| b) = true then 1 else 2) (hcr : c ≤ r) :
    Safe (r - c) (Pnext P (a ||| b)) := by
  match r, hs with
  | 0, _ => split at hcost <;> omega
  | 1, hs =>
    have hw : wideB (a ||| b) = true := by
      by_contra hw; rw [if_neg hw] at hcost; omega
    rw [if_pos hw] at hcost; subst hcost
    exact hs.2 a b ha hb hn hw
  | k+2, hs =>
    by_cases hw : wideB (a ||| b) = true
    · rw [if_pos hw] at hcost; subst hcost
      exact (hs.2 a b ha hb hn).1 hw
    · rw [if_neg hw] at hcost; subst hcost
      exact (hs.2 a b ha hb hn).2 (by simpa using hw)

theorem realizeOR (hsafe : Safe 5 (· ∈ initList)) : ∀ G : List F, good G → wsum G ≤ 5 →
    ∃ P : ℕ → Prop, Closed P ∧ P TOP ∧ (∀ f ∈ G ++ inputs, ∃ a, P a ∧ rep f a) ∧
      Safe (5 - wsum G) P
  | [], _, _ => by
    refine ⟨(· ∈ initList), initList_closed, by decide, ?_, hsafe⟩
    intro f hf
    simp only [List.nil_append, inputs, List.mem_cons, List.mem_ofFn] at hf
    rcases hf with rfl | ⟨i, rfl⟩
    · exact ⟨0, by decide, rep_zero⟩
    · exact ⟨Xs i, by fin_cases i <;> decide, rep_input i⟩
  | g :: G, hg, hw => by
    obtain ⟨⟨u, v, hu, hv, he⟩, hG⟩ := hg
    have hwsum0 : wsum (g :: G) = wsum G + (if wideF g then 1 else 2) := rfl
    have hwG : wsum G ≤ 5 := by
      have := hw; rw [hwsum0] at this; split at this <;> omega
    obtain ⟨P, hc, htop, hcov, hs⟩ := realizeOR hsafe G hG hwG
    have hcov' : ∀ f ∈ G ++ inputs, ∃ a, P a ∧ rep f a := hcov
    obtain ⟨a, ha, ea⟩ := cl_rep hc htop hcov' hu
    obtain ⟨b, hb, eb⟩ := cl_rep hc htop hcov' hv
    have eg : rep g (a ||| b) := by
      have := rep_or ea eb
      intro j; rw [this j, he]
    have hcost : (if wideF g then 1 else 2) = if wideB (a ||| b) = true then 1 else 2 := by
      by_cases hwg : wideF g
      · rw [if_pos hwg, if_pos ((wide_link eg).mp hwg)]
      · rw [if_neg hwg, if_neg (fun h' => hwg ((wide_link eg).mpr h'))]
    have hcovg : ∀ Q : ℕ → Prop, (∀ x, P x → Q x) → Q (a ||| b) →
        ∀ f ∈ (g :: G) ++ inputs, ∃ a, Q a ∧ rep f a := by
      intro Q hPQ hQ f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨a ||| b, hQ, eg⟩
      · obtain ⟨t, ht, et⟩ := hcov f hf
        exact ⟨t, hPQ t ht, et⟩
    by_cases hz : P (a ||| b)
    · refine ⟨P, hc, htop, hcovg P (fun _ h => h) hz, safe_mono' ?_ hs⟩
      rw [hwsum0]; omega
    · refine ⟨Pnext P (a ||| b), closed_next hc _, Or.inl htop,
        hcovg _ (fun _ h => Or.inl h) (Or.inr (Or.inl rfl)), ?_⟩
      have hwsum : wsum (g :: G) = wsum G + (if wideF g then 1 else 2) := rfl
      rw [hwsum, hcost] at hw ⊢
      have := safe_step (c := if wideB (a ||| b) = true then 1 else 2) hs ha hb hz rfl
        (by by_cases hwz : wideB (a ||| b) = true <;> simp only [hwz, if_true, if_false,
          Bool.false_eq_true] at hw ⊢ <;> omega)
      rwa [show 5 - (wsum G + if wideB (a ||| b) = true then 1 else 2) =
        5 - wsum G - (if wideB (a ||| b) = true then 1 else 2) by omega]

theorem orHalf (hsafe : Safe 5 (· ∈ initList)) (C : Circuit) (B D : Finset ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (he : ∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5,
      (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true))
    (hB : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → IsWide C.gates j → j ∈ B)
    (hD : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → ¬ IsWide C.gates j → j ∈ D) :
    6 ≤ B.card + 2 * D.card := by
  by_contra hlt
  obtain ⟨G, hg, hlen, hw⟩ := invOR B D C.gates (fun g hmem => by
    obtain ⟨hop, hl⟩ := hm g hmem
    exact ⟨by simpa [Set.mem_insert_iff, or_comm] using hop, hl⟩) hB hD
  have h1 := Finset.card_filter_le B (fun j => j < C.gates.length)
  have h2 := Finset.card_filter_le D (fun j => j < C.gates.length)
  obtain ⟨P, hc, htop, hcov, hs⟩ := realizeOR hsafe G hg (by omega)
  obtain ⟨v, hv, ev⟩ := cl_rep hc htop hcov (hw C.output)
  have eq : v = T := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [ev j, target_table j]
    congr 1
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact he (sample j))
  exact safe_excl hs (eq ▸ hv)

-- The AND half: OR gates are free, every AND gate costs one.

def inputsA : List F := (fun _ => true) :: List.ofFn (fun i x => x i)

def clA (G : List F) (w : F) : Prop :=
  ∃ S : List F, (∀ f ∈ S, f ∈ G ++ inputsA) ∧ ∀ x, w x = S.any (fun f => f x)

def goodA : List F → Prop
  | [] => True
  | g :: G => (∃ u v, clA G u ∧ clA G v ∧ ∀ x, g x = (u x && v x)) ∧ goodA G

theorem memberA {G : List F} {f : F} (h : f ∈ G ++ inputsA) : clA G f :=
  ⟨[f], by simpa using h, by simp⟩

theorem clA_congr {G : List F} {u v : F} (hu : clA G u) (h : ∀ x, v x = u x) : clA G v := by
  obtain ⟨S, hs, he⟩ := hu
  exact ⟨S, hs, fun x => (h x).trans (he x)⟩

theorem clA_new (G : List F) (f : F) : clA (f :: G) f := memberA (by simp)

theorem clA_mono {G : List F} {f : F} (g : F) (h : clA G f) : clA (g :: G) f := by
  obtain ⟨S, hs, he⟩ := h
  exact ⟨S, fun v hv => List.mem_cons_of_mem _ (hs v hv), he⟩

theorem clA_false (G : List F) : clA G (fun _ => false) := ⟨[], by simp, by simp⟩

theorem clA_true (G : List F) : clA G (fun _ => true) := memberA (by simp [inputsA])

theorem clA_or {G : List F} {a b : F} (ha : clA G a) (hb : clA G b) :
    clA G (fun x => a x || b x) := by
  obtain ⟨A,hA,eA⟩ := ha
  obtain ⟨B,hB,eB⟩ := hb
  exact ⟨A ++ B, fun g hg => (List.mem_append.mp hg).elim (hA g) (hB g),
    fun x => by simp [eA x, eB x]⟩

theorem gateA_or (G : List F) (f : ℕ → F)
    (hw : ∀ k, clA G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    clA G (fun x => GateOp.eval GateOp.or (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact clA_congr (clA_false G) (fun x => by simp [GateOp.eval])
  · exact clA_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact clA_congr (clA_or (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

theorem gateA_and (G : List F) (f : ℕ → F)
    (hw : ∀ k, clA G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, clA G u ∧ clA G v ∧
      ∀ x, GateOp.eval GateOp.and (ins.map fun i => f i x) = (u x && v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => true, fun _ => true, clA_true G, clA_true G,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

theorem baseA (k : ℕ) : clA [] (wf [] k) := by
  by_cases hk : k < 5
  · apply clA_congr (memberA (G := []) (f := fun x => x ⟨k,hk⟩) (by interval_cases k <;> simp [inputsA]))
    intro x
    interval_cases k <;> rfl
  · apply clA_congr (clA_false [])
    intro x
    simp [wf, W, List.getD_eq_getElem?_getD, hk]

theorem invAND (A : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.or ∨ g.op = GateOp.and) ∧ g.inputs.length ≤ 2)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ G, goodA G ∧ G.length ≤ (A.filter (fun j => j < gs.length)).card ∧
      ∀ k, clA G (wf gs k) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], trivial, by simp, fun k => baseA k⟩
  | append_singleton gs g ih =>
    obtain ⟨G, hG, hlen, hw⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
      (fun j g' hj ho => hA j g' (by
        have hjl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [List.getElem?_append_left hjl]; exact hj) ho)
    obtain ⟨hop, hl⟩ := hm g (by simp)
    have hAm := card_mono A gs.length
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at *
    rcases hop with hop | hop
    · refine ⟨G, hG, by omega, ?_⟩
      intro k
      rw [wf_snoc, hop]
      by_cases hk : k = 5 + gs.length
      · rw [if_pos hk]; exact gateA_or G (wf gs) hw g.inputs hl
      · rw [if_neg hk]; exact hw k
    · obtain ⟨u, v, hu, hv, he⟩ := gateA_and G (wf gs) hw g.inputs hl
      have hmem : gs.length ∈ A := hA gs.length g (by simp) hop
      refine ⟨(fun x => GateOp.eval GateOp.and (g.inputs.map fun i => wf gs i x)) :: G,
        ⟨⟨u, v, hu, hv, he⟩, hG⟩, ?_, ?_⟩
      · have := card_step A gs.length hmem
        simp only [List.length_cons]; omega
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 5 + gs.length
        · rw [if_pos hk]; exact clA_new _ _
        · rw [if_neg hk]; exact clA_mono _ (hw k)

-- search for the AND half
def PnextA (Q : ℕ → Prop) (z : ℕ) : ℕ → Prop := fun x => Q x ∨ x = z ∨ ∃ b, Q b ∧ x = b ||| z

def ClosedA (Q : ℕ → Prop) : Prop := ∀ a b, Q a → Q b → Q (a ||| b)

theorem closedA_next {Q : ℕ → Prop} (hc : ClosedA Q) (z : ℕ) : ClosedA (PnextA Q z) := by
  intro a b ha hb
  rcases ha with ha | rfl | ⟨p, hp, rfl⟩ <;> rcases hb with hb | rfl | ⟨q, hq, rfl⟩
  · exact Or.inl (hc _ _ ha hb)
  · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
  · exact Or.inr (Or.inr ⟨a ||| q, hc _ _ ha hq, by rw [bOrAssoc]⟩)
  · exact Or.inr (Or.inr ⟨b, hb, bOrComm _ _⟩)
  · exact Or.inr (Or.inl (bOrSelf _))
  · exact Or.inr (Or.inr ⟨q, hq, by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_lor]
      cases q.testBit i <;> cases a.testBit i <;> rfl⟩)
  · exact Or.inr (Or.inr ⟨p ||| b, hc _ _ hp hb, by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_lor]
      cases p.testBit i <;> cases b.testBit i <;> cases z.testBit i <;> rfl⟩)
  · exact Or.inr (Or.inr ⟨p, hp, by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_lor]
      cases p.testBit i <;> cases b.testBit i <;> rfl⟩)
  · exact Or.inr (Or.inr ⟨p ||| q, hc _ _ hp hq, by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_lor]
      cases p.testBit i <;> cases q.testBit i <;> cases z.testBit i <;> rfl⟩)

def SafeA : ℕ → (ℕ → Prop) → Prop
  | 0, Q => ¬ Q T
  | k+1, Q => ¬ Q T ∧ ∀ a b, Q a → Q b → ¬ Q (a &&& b) → SafeA k (PnextA Q (a &&& b))

theorem safeA_excl {k : ℕ} {Q : ℕ → Prop} (h : SafeA k Q) : ¬ Q T := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem safeA_mono : ∀ (k : ℕ) (Q : ℕ → Prop), SafeA (k+1) Q → SafeA k Q
  | 0, _, h => h.1
  | k+1, _, h => ⟨h.1, fun a b ha hb hn => safeA_mono k _ (h.2 a b ha hb hn)⟩

def mapOr (v : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => (b ||| v) :: mapOr v bs

def nextLA (L : List ℕ) (S : ℕ) (v : ℕ) : List ℕ × ℕ :=
  if inS S v then (L, S) else addAll (v :: mapOr v L) L S

theorem mapOr_mem (v y : ℕ) : ∀ L : List ℕ, y ∈ mapOr v L ↔ ∃ b, b ∈ L ∧ y = b ||| v
  | [] => by simp [mapOr]
  | b :: bs => by
    simp only [mapOr, List.mem_cons, mapOr_mem v y bs]
    constructor
    · rintro (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨b, Or.inl rfl, rfl⟩
      · exact ⟨c, Or.inr hc, rfl⟩
    · rintro ⟨c, rfl | hc, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨c, hc, rfl⟩

theorem nextLA_spec {L : List ℕ} {S : ℕ} (h : Inv L S) (hc : ClosedA (· ∈ L)) (v : ℕ) :
    Inv (nextLA L S v).1 (nextLA L S v).2 ∧
      ∀ y, y ∈ (nextLA L S v).1 ↔ PnextA (· ∈ L) v y := by
  unfold nextLA
  by_cases hv : inS S v = true
  · rw [if_pos hv]
    have hvL := (h v).mp hv
    refine ⟨h, fun y => ⟨fun hy => Or.inl hy, ?_⟩⟩
    rintro (hy | rfl | ⟨b, hb, rfl⟩)
    · exact hy
    · exact hvL
    · exact hc _ _ hb hvL
  · rw [if_neg hv]
    obtain ⟨h1, h2⟩ := addAll_spec (v :: mapOr v L) L S h
    refine ⟨h1, fun y => ?_⟩
    rw [h2, List.mem_cons, mapOr_mem]
    rfl

def optRowA (S a : ℕ) : List ℕ → List ℕ → ℕ → List ℕ × ℕ
  | [], o, O => (o, O)
  | b :: bs, o, O =>
      if inS S (a &&& b) || inS O (a &&& b) then optRowA S a bs o O
      else optRowA S a bs ((a &&& b) :: o) (O ||| (1 <<< (a &&& b)))

def optAllA (S : ℕ) : List ℕ → List ℕ → ℕ → List ℕ × ℕ
  | [], o, O => (o, O)
  | a :: as, o, O => optAllA S as (optRowA S a as o O).1 (optRowA S a as o O).2

theorem optRowA_spec (S a : ℕ) : ∀ (bs o : List ℕ) (O : ℕ), Inv o O →
    Inv (optRowA S a bs o O).1 (optRowA S a bs o O).2 ∧ (∀ z ∈ o, z ∈ (optRowA S a bs o O).1) ∧
      ∀ b ∈ bs, inS S (a &&& b) = false → (a &&& b) ∈ (optRowA S a bs o O).1
  | [], o, O, h => ⟨h, fun _ hz => hz, by simp⟩
  | b :: bs, o, O, h => by
    unfold optRowA
    split
    · rename_i hc
      obtain ⟨h1, h2, h3⟩ := optRowA_spec S a bs o O h
      refine ⟨h1, h2, fun b' hb' hS => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · rw [hS, Bool.false_or] at hc
        exact h2 _ ((h _).mp hc)
      · exact h3 b' hb' hS
    · have hinv : Inv ((a &&& b) :: o) (O ||| (1 <<< (a &&& b))) := by
        intro y
        rw [inS_add, Bool.or_eq_true, h, decide_eq_true_eq, List.mem_cons]
        tauto
      obtain ⟨h1, h2, h3⟩ := optRowA_spec S a bs _ _ hinv
      refine ⟨h1, fun z hz => h2 z (List.mem_cons_of_mem _ hz), fun b' hb' hS => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h2 _ (List.mem_cons_self ..)
      · exact h3 b' hb' hS

theorem optAllA_spec (S : ℕ) : ∀ (L o : List ℕ) (O : ℕ), Inv o O → (∀ a ∈ L, inS S a = true) →
    Inv (optAllA S L o O).1 (optAllA S L o O).2 ∧ (∀ z ∈ o, z ∈ (optAllA S L o O).1) ∧
      ∀ a ∈ L, ∀ b ∈ L, inS S (a &&& b) = false → (a &&& b) ∈ (optAllA S L o O).1
  | [], o, O, h, _ => ⟨h, fun _ hz => hz, by simp⟩
  | a :: as, o, O, h, hL => by
    unfold optAllA
    obtain ⟨r1, r2, r3⟩ := optRowA_spec S a as o O h
    obtain ⟨q1, q2, q3⟩ := optAllA_spec S as _ _ r1 (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    refine ⟨q1, fun z hz => q2 z (r2 z hz), fun x hx y hy hS => ?_⟩
    rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
    · rw [hx, hy, bAndSelf, hL a (List.mem_cons_self ..)] at hS; exact absurd hS (by simp)
    · rw [hx] at hS ⊢; exact q2 _ (r3 y hy hS)
    · rw [hy, bAndComm] at hS ⊢; exact q2 _ (r3 x hx hS)
    · exact q3 x hx y hy hS

-- largest element below T
def cdown : List ℕ → ℕ → ℕ
  | [], c => c
  | x :: xs, c => cdown xs (if Nat.beq (x &&& T) x then c ||| x else c)

theorem cdown_spec : ∀ (xs : List ℕ) (c : ℕ), c &&& T = c →
    cdown xs c &&& T = cdown xs c ∧ c &&& cdown xs c = c ∧
      ∀ x ∈ xs, x &&& T = x → x &&& cdown xs c = x
  | [], c, h => ⟨h, bAndSelf c, by simp⟩
  | x :: xs, c, h => by
    set c' := (if Nat.beq (x &&& T) x then c ||| x else c) with hc'
    have hc'T : c' &&& T = c' := by
      rw [hc']; split
      · rename_i hb
        have hx : x &&& T = x := by simpa using hb
        rw [bAndComm, bAndOr, bAndComm, h, bAndComm, hx]
      · exact h
    obtain ⟨r1, r2, r3⟩ := cdown_spec xs c' hc'T
    simp only [cdown]
    rw [← hc']
    have hcc' : c &&& c' = c := by
      rw [hc']; split
      · exact bAbsorb c x
      · exact bAndSelf c
    refine ⟨r1, by rw [← hcc', bAndAssoc, r2], ?_⟩
    intro y hy hyT
    rcases List.mem_cons.mp hy with hy | hy
    · rw [hy] at hyT ⊢
      have hb : Nat.beq (x &&& T) x = true := beq_of_eq hyT
      have hxc' : x &&& c' = x := by
        rw [hc', if_pos hb, bOrComm, bAbsorb]
      rw [← hxc', bAndAssoc, r2]
    · exact r3 y hy hyT

def leafA (L : List ℕ) (S : ℕ) : Bool :=
  !inS S T && !(L.any fun a => L.any fun b => Nat.beq (cdown L 0 ||| (a &&& b)) T)

def checkA2 (L : List ℕ) (S : ℕ) : Bool :=
  leafA L S && (optAllA S L [] 0).1.all (fun z => leafA (nextLA L S z).1 (nextLA L S z).2)

theorem leafA_sound {L : List ℕ} {S : ℕ} (hinv : Inv L S) (h : leafA L S = true) :
    SafeA 1 (· ∈ L) := by
  unfold leafA at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  obtain ⟨h0, hp⟩ := h
  have hT : ¬ T ∈ L := fun hm => by rw [(hinv T).mpr hm] at h0; exact absurd h0 (by simp)
  obtain ⟨d1, _, d3⟩ := cdown_spec L 0 (by simp)
  set cd := cdown L 0
  refine ⟨hT, fun a b ha hb _ hn => ?_⟩
  have key : cd ||| (a &&& b) = T := by
    rcases hn with hn | hn | ⟨q, hq, hn⟩
    · exact absurd hn hT
    · rw [← hn, bOrComm]
      apply Nat.eq_of_testBit_eq; intro i
      have := congrArg (fun n => Nat.testBit n i) d1
      simp only [Nat.testBit_land, Nat.testBit_lor] at this ⊢
      cases hc : cd.testBit i <;> cases ht : T.testBit i <;> simp_all
    · have hqT : q &&& T = q := by rw [hn, bAbsorb]
      have hqc := d3 q hq hqT
      rw [hn]
      apply Nat.eq_of_testBit_eq; intro i
      have e1 := congrArg (fun n => Nat.testBit n i) d1
      have e2 := congrArg (fun n => Nat.testBit n i) hqc
      have e3 := congrArg (fun n => Nat.testBit n i) hn
      simp only [Nat.testBit_land, Nat.testBit_lor] at e1 e2 e3 ⊢
      cases hc : cd.testBit i <;> cases hq' : q.testBit i <;> cases ha' : a.testBit i <;>
        cases hb' : b.testBit i <;> cases ht : T.testBit i <;> simp_all
  exact hp a ha (List.any_eq_true.mpr ⟨b, hb, beq_of_eq key⟩)

theorem checkA2_sound {L : List ℕ} {S : ℕ} (hinv : Inv L S) (hc : ClosedA (· ∈ L))
    (h : checkA2 L S = true) : SafeA 2 (· ∈ L) := by
  unfold checkA2 at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  refine ⟨(leafA_sound hinv h0).1, fun a b ha hb hn => ?_⟩
  obtain ⟨_, _, h3⟩ := optAllA_spec S L [] 0 inv_nil (fun x hx => (hinv x).mpr hx)
  have hz : (a &&& b) ∈ (optAllA S L [] 0).1 := by
    apply h3 a ha b hb
    cases hs : inS S (a &&& b)
    · rfl
    · exact absurd ((hinv _).mp hs) hn
  obtain ⟨c1, c2⟩ := nextLA_spec hinv hc (a &&& b)
  have heq : (fun y => y ∈ (nextLA L S (a &&& b)).1) = PnextA (· ∈ L) (a &&& b) :=
    funext fun y => propext (c2 y)
  rw [← heq]
  exact leafA_sound c1 (hall _ hz)

def initA : List ℕ := [0, 353, 3848, 3945, 5282, 5603, 8106, 8171, 10436, 10725, 12236, 12269,
  12816, 13169, 14002, 14323, 15060, 15349, 15590, 15847, 16118, 16152, 16249, 16314, 16348,
  16366, 16367, 16375, 16379, 16381, 16382, 16383]

theorem initA_closed : ClosedA (· ∈ initA) := by
  have h : initA.all (fun a => initA.all (fun b => initA.contains (a ||| b))) = true := by
    decide
  intro a b ha hb
  simp only [List.all_eq_true, List.contains_iff_mem] at h
  exact h a ha b hb

theorem clA_rep {Q : ℕ → Prop} {G : List F} {w : F} (hc : ClosedA Q) (h0 : Q 0)
    (hG : ∀ f ∈ G ++ inputsA, ∃ a, Q a ∧ rep f a) (hw : clA G w) : ∃ a, Q a ∧ rep w a := by
  obtain ⟨S, hS, he⟩ := hw
  have aux : ∀ U : List F, (∀ f ∈ U, f ∈ G ++ inputsA) →
      ∃ a, Q a ∧ rep (fun x => U.any (fun f => f x)) a := by
    intro U hU
    induction U with
    | nil => exact ⟨0, h0, by simpa using rep_zero⟩
    | cons f U ih =>
      obtain ⟨a, ha, ea⟩ := hG f (hU f (by simp))
      obtain ⟨b, hb, eb⟩ := ih (fun t ht => hU t (List.mem_cons_of_mem _ ht))
      exact ⟨a ||| b, hc _ _ ha hb, by simpa [List.any_cons] using rep_or ea eb⟩
  obtain ⟨a, ha, ea⟩ := aux S hS
  exact ⟨a, ha, fun j => by rw [ea j]; congr 1; exact (he _).symm⟩

theorem safeA_mono' {k j : ℕ} {Q : ℕ → Prop} (hjk : j ≤ k) (h : SafeA k Q) : SafeA j Q := by
  induction k with
  | zero => rwa [Nat.le_zero.mp hjk]
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hjk with hlt | heq
    · exact ih (by omega) (safeA_mono k Q h)
    · rwa [heq]

theorem realizeA (hsafe : SafeA 2 (· ∈ initA)) : ∀ G : List F, goodA G → G.length ≤ 2 →
    ∃ Q : ℕ → Prop, ClosedA Q ∧ Q 0 ∧ (∀ f ∈ G ++ inputsA, ∃ a, Q a ∧ rep f a) ∧
      SafeA (2 - G.length) Q
  | [], _, _ => by
    refine ⟨(· ∈ initA), initA_closed, by decide, ?_, hsafe⟩
    intro f hf
    simp only [List.nil_append, inputsA, List.mem_cons, List.mem_ofFn] at hf
    rcases hf with rfl | ⟨i, rfl⟩
    · exact ⟨TOP, by decide, rep_top⟩
    · exact ⟨Xs i, by fin_cases i <;> decide, rep_input i⟩
  | g :: G, hg, hl => by
    obtain ⟨⟨u, v, hu, hv, he⟩, hG⟩ := hg
    simp only [List.length_cons] at hl ⊢
    obtain ⟨Q, hc, h0, hcov, hs⟩ := realizeA hsafe G hG (by omega)
    obtain ⟨a, ha, ea⟩ := clA_rep hc h0 hcov hu
    obtain ⟨b, hb, eb⟩ := clA_rep hc h0 hcov hv
    have eg : rep g (a &&& b) := by
      have := rep_and ea eb
      intro j; rw [this j, he]
    have hcovg : ∀ R : ℕ → Prop, (∀ x, Q x → R x) → R (a &&& b) →
        ∀ f ∈ (g :: G) ++ inputsA, ∃ a, R a ∧ rep f a := by
      intro R hQR hR f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨a &&& b, hR, eg⟩
      · obtain ⟨t, ht, et⟩ := hcov f hf
        exact ⟨t, hQR t ht, et⟩
    by_cases hz : Q (a &&& b)
    · exact ⟨Q, hc, h0, hcovg Q (fun _ h => h) hz, safeA_mono' (by omega) hs⟩
    · refine ⟨PnextA Q (a &&& b), closedA_next hc _, Or.inl h0,
        hcovg _ (fun _ h => Or.inl h) (Or.inr (Or.inl rfl)), ?_⟩
      rw [show 2 - G.length = (2 - (G.length + 1)) + 1 by omega] at hs
      exact hs.2 a b ha hb hz

theorem andHalf (hsafe : SafeA 2 (· ∈ initA)) (C : Circuit) (A : Finset ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (he : ∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5,
      (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true))
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    3 ≤ A.card := by
  by_contra hlt
  obtain ⟨G, hg, hlen, hw⟩ := invAND A C.gates (fun g hmem => by
    obtain ⟨hop, hl⟩ := hm g hmem
    exact ⟨by simpa [Set.mem_insert_iff, or_comm] using hop, hl⟩) hA
  have h1 := Finset.card_filter_le A (fun j => j < C.gates.length)
  obtain ⟨Q, hc, h0, hcov, hs⟩ := realizeA hsafe G hg (by omega)
  obtain ⟨v, hv, ev⟩ := clA_rep hc h0 hcov (hw C.output)
  have eq : v = T := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [ev j, target_table j]
    congr 1
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact he (sample j))
  exact safeA_excl hs (eq ▸ hv)

-- the two searches, as states with bitsets

def initS : List ℕ × ℕ := addAll initList [] 0
def initAS : List ℕ × ℕ := addAll initA [] 0

theorem initS_mem : ∀ y, y ∈ initS.1 ↔ y ∈ initList := by
  intro y; rw [initS, (addAll_spec initList [] 0 inv_nil).2 y]; simp

theorem initAS_mem : ∀ y, y ∈ initAS.1 ↔ y ∈ initA := by
  intro y; rw [initAS, (addAll_spec initA [] 0 inv_nil).2 y]; simp

theorem safe_of_check (h : check 5 initS.1 initS.2 = true) : Safe 5 (· ∈ initList) := by
  have heq : (fun y => y ∈ initS.1) = (· ∈ initList) := funext fun y => propext (initS_mem y)
  have hc : Closed (· ∈ initS.1) := by rw [heq]; exact initList_closed
  have := check_sound 5 initS.1 initS.2 (addAll_spec initList [] 0 inv_nil).1 hc
    ((initS_mem TOP).mpr (by decide)) h
  rwa [heq] at this

theorem safeA_of_check (h : checkA2 initAS.1 initAS.2 = true) : SafeA 2 (· ∈ initA) := by
  have heq : (fun y => y ∈ initAS.1) = (· ∈ initA) := funext fun y => propext (initAS_mem y)
  have hc : ClosedA (· ∈ initAS.1) := by rw [heq]; exact initA_closed
  have := checkA2_sound (addAll_spec initA [] 0 inv_nil).1 hc h
  rw [← heq]; exact this

-- The kernel computations.

theorem kernelA : checkA2 initAS.1 initAS.2 = true := by decide +kernel

def f5 (z : ℕ) : Bool :=
  if wideB z then check 4 (nextL initS.1 initS.2 z).1 (nextL initS.1 initS.2 z).2
  else check 3 (nextL initS.1 initS.2 z).1 (nextL initS.1 initS.2 z).2

def opts5 : List ℕ := [96, 160, 192, 288, 320, 384, 481, 544, 576, 640, 768, 865, 1056, 1088, 1152, 1280, 1377, 1536, 2080, 2112, 2176, 2304, 2401, 2560, 3072, 3880, 3912, 3976, 3945, 4128, 4160, 4224, 4352, 4449, 4608, 5120, 6144, 7944, 5346, 5538, 5603, 5794, 7330, 8106, 8224, 8256, 8320, 8448, 8545, 8704, 9216, 10240, 12040, 12288, 13474, 10468, 10692, 10725, 10948, 11460, 12236, 14532, 15590, 12848, 12880, 12944, 13072, 13169, 13840, 14864, 16152, 14002, 15060]

theorem opts5_eq : (optAll initS.2 initS.1 [] 0).1 = opts5 := by decide +kernel

theorem k5_0 : f5 96 = true := by decide +kernel
theorem k5_1 : f5 160 = true := by decide +kernel
theorem k5_2 : f5 192 = true := by decide +kernel
theorem k5_3 : f5 288 = true := by decide +kernel
theorem k5_4 : f5 320 = true := by decide +kernel
theorem k5_5 : f5 384 = true := by decide +kernel
theorem k5_6 : f5 481 = true := by decide +kernel
theorem k5_7 : f5 544 = true := by decide +kernel
theorem k5_8 : f5 576 = true := by decide +kernel
theorem k5_9 : f5 640 = true := by decide +kernel
theorem k5_10 : f5 768 = true := by decide +kernel
theorem k5_11 : f5 865 = true := by decide +kernel
theorem k5_12 : f5 1056 = true := by decide +kernel
theorem k5_13 : f5 1088 = true := by decide +kernel
theorem k5_14 : f5 1152 = true := by decide +kernel
theorem k5_15 : f5 1280 = true := by decide +kernel
theorem k5_16 : f5 1377 = true := by decide +kernel
theorem k5_17 : f5 1536 = true := by decide +kernel
theorem k5_18 : f5 2080 = true := by decide +kernel
theorem k5_19 : f5 2112 = true := by decide +kernel
theorem k5_20 : f5 2176 = true := by decide +kernel
theorem k5_21 : f5 2304 = true := by decide +kernel
theorem k5_22 : f5 2401 = true := by decide +kernel
theorem k5_23 : f5 2560 = true := by decide +kernel
theorem k5_24 : f5 3072 = true := by decide +kernel
theorem k5_25 : f5 3880 = true := by decide +kernel
theorem k5_26 : f5 3912 = true := by decide +kernel
theorem k5_27 : f5 3976 = true := by decide +kernel
theorem k5_28 : f5 3945 = true := by decide +kernel
theorem k5_29 : f5 4128 = true := by decide +kernel
theorem k5_30 : f5 4160 = true := by decide +kernel
theorem k5_31 : f5 4224 = true := by decide +kernel
theorem k5_32 : f5 4352 = true := by decide +kernel
theorem k5_33 : f5 4449 = true := by decide +kernel
theorem k5_34 : f5 4608 = true := by decide +kernel
theorem k5_35 : f5 5120 = true := by decide +kernel
theorem k5_36 : f5 6144 = true := by decide +kernel
theorem k5_37 : f5 7944 = true := by decide +kernel
theorem k5_38 : f5 5346 = true := by decide +kernel
theorem k5_39 : f5 5538 = true := by decide +kernel
theorem k5_40 : f5 5603 = true := by decide +kernel
theorem k5_41 : f5 5794 = true := by decide +kernel
theorem k5_42 : f5 7330 = true := by decide +kernel
theorem k5_43 : f5 8106 = true := by decide +kernel
theorem k5_44 : f5 8224 = true := by decide +kernel
theorem k5_45 : f5 8256 = true := by decide +kernel
theorem k5_46 : f5 8320 = true := by decide +kernel
theorem k5_47 : f5 8448 = true := by decide +kernel
theorem k5_48 : f5 8545 = true := by decide +kernel
theorem k5_49 : f5 8704 = true := by decide +kernel
theorem k5_50 : f5 9216 = true := by decide +kernel
theorem k5_51 : f5 10240 = true := by decide +kernel
theorem k5_52 : f5 12040 = true := by decide +kernel
theorem k5_53 : f5 12288 = true := by decide +kernel
theorem k5_54 : f5 13474 = true := by decide +kernel
theorem k5_55 : f5 10468 = true := by decide +kernel
theorem k5_56 : f5 10692 = true := by decide +kernel
theorem k5_57 : f5 10725 = true := by decide +kernel
theorem k5_58 : f5 10948 = true := by decide +kernel
theorem k5_59 : f5 11460 = true := by decide +kernel
theorem k5_60 : f5 12236 = true := by decide +kernel
theorem k5_61 : f5 14532 = true := by decide +kernel
theorem k5_62 : f5 15590 = true := by decide +kernel
theorem k5_63 : f5 12848 = true := by decide +kernel
theorem k5_64 : f5 12880 = true := by decide +kernel
theorem k5_65 : f5 12944 = true := by decide +kernel
theorem k5_66 : f5 13072 = true := by decide +kernel
theorem k5_67 : f5 13169 = true := by decide +kernel
theorem k5_68 : f5 13840 = true := by decide +kernel
theorem k5_69 : f5 14864 = true := by decide +kernel
theorem k5_70 : f5 16152 = true := by decide +kernel
theorem k5_71 : f5 14002 = true := by decide +kernel
theorem k5_72 : f5 15060 = true := by decide +kernel

theorem kernelT : inS initS.2 T = false := by decide +kernel

theorem kernel5 : check 5 initS.1 initS.2 = true := by
  have h : check 5 initS.1 initS.2 = (!inS initS.2 T && (optAll initS.2 initS.1 [] 0).1.all f5) := rfl
  rw [h, opts5_eq, kernelT]
  simp only [opts5, List.all_cons, List.all_nil, k5_0, k5_1, k5_2, k5_3, k5_4, k5_5, k5_6, k5_7, k5_8, k5_9, k5_10, k5_11, k5_12, k5_13, k5_14, k5_15, k5_16, k5_17, k5_18, k5_19, k5_20, k5_21, k5_22, k5_23, k5_24, k5_25, k5_26, k5_27, k5_28, k5_29, k5_30, k5_31, k5_32, k5_33, k5_34, k5_35, k5_36, k5_37, k5_38, k5_39, k5_40, k5_41, k5_42, k5_43, k5_44, k5_45, k5_46, k5_47, k5_48, k5_49, k5_50, k5_51, k5_52, k5_53, k5_54, k5_55, k5_56, k5_57, k5_58, k5_59, k5_60, k5_61, k5_62, k5_63, k5_64, k5_65, k5_66, k5_67, k5_68, k5_69, k5_70, k5_71, k5_72, Bool.not_false, Bool.and_true]

end PEqualNP.Outside.L_meta_701

theorem PEqualNP.Outside.L_meta_701 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ D) → 9 ≤ A.card + B.card + 2 * D.card := by
  intro C A B D hm he hA hB hD
  have h1 := PEqualNP.Outside.L_meta_701.andHalf
    (PEqualNP.Outside.L_meta_701.safeA_of_check PEqualNP.Outside.L_meta_701.kernelA) C A hm he hA
  have h2 := PEqualNP.Outside.L_meta_701.orHalf
    (PEqualNP.Outside.L_meta_701.safe_of_check PEqualNP.Outside.L_meta_701.kernel5) C B D hm he
    (fun j g h1 h2 h3 => hB j g h1 h2 h3) (fun j g h1 h2 h3 => hD j g h1 h2 h3)
  omega
