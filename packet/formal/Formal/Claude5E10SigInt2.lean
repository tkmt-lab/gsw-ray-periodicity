import Formal.Claude5E10SigInt

/-!
# E10 as a Theorem 1a signature: corners, edges and triangles in one chart

Written by a Claude worker (2026-10-21, E10 bridge session).

* `corner_site` : every corner vertex is the vertex of one of the twelve marked chart points;
* `chart_pair` : a unit step of a model chart is a unit step of one signature chart;
* `chart_tri` : likewise for a unit triangle.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The chart of mark `k`. -/
def cornF (k : ℕ) : ℕ := if k < 6 then 0 else 1

/-- The position of mark `k` (lower corners `L0 L1 … L5`, then upper `U0 U5 U4 U3 U2 U1`). -/
def cornZ (r s : ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (r, 0)
  | 2 => (r, r + s)
  | 3 => (0, 2 * r + s)
  | 4 => (-(r + s), 2 * r + s)
  | 5 => (-(r + s), r + s)
  | 6 => (0, 0)
  | 7 => (r + s, 0)
  | 8 => (r + s, r)
  | 9 => (0, 2 * r + s)
  | 10 => (-r, 2 * r + s)
  | _ => (-r, r)

theorem chL_bd {z : ℤ × ℤ} {a : ℤ} (hb : ¬ IL r s z) (ha : aL r s z = a) :
    ch p r s w 0 z = (2, (a, 0)) := by rw [chL_B hb, ha]

theorem chU_bd {z : ℤ × ℤ} {a : ℤ} (hb : ¬ IU r s z) (ha : aU r s z = a) :
    ch p r s w 1 z = (2, (wrap r s (a + w), 2 * p)) := by rw [chU_B hb, ha]

/-- **Corners are marked.** -/
theorem corner_site (H : Hyp p r s w) {v : MV} (h : IsCornerV p r s w v) :
    ∃ k, k < 12 ∧ QD p r s (cornF k) (cornZ r s k) ∧ ch p r s w (cornF k) (cornZ r s k) = v := by
  have hr := H.hr; have hs := H.hs
  rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> simp only [IsArc] at ha
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨0, by omega, ?_, chL_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HL, if_true, if_false]; e10om
      · simp only [cornZ, IL]; e10om
      · simp only [cornZ, aL]; split_ifs <;> e10om
    · refine ⟨5, by omega, ?_, chL_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HL, if_true, if_false]; e10om
      · simp only [cornZ, IL]; e10om
      · simp only [cornZ, aL]; split_ifs <;> e10om
    · refine ⟨4, by omega, ?_, chL_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HL, if_true, if_false]; e10om
      · simp only [cornZ, IL]; e10om
      · simp only [cornZ, aL]; split_ifs <;> e10om
    · refine ⟨3, by omega, ?_, chL_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HL, if_true, if_false]; e10om
      · simp only [cornZ, IL]; e10om
      · simp only [cornZ, aL]; split_ifs <;> e10om
    · refine ⟨2, by omega, ?_, chL_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HL, if_true, if_false]; e10om
      · simp only [cornZ, IL]; e10om
      · simp only [cornZ, aL]; split_ifs <;> e10om
    · refine ⟨1, by omega, ?_, chL_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HL, if_true, if_false]; e10om
      · simp only [cornZ, IL]; e10om
      · simp only [cornZ, aL]; split_ifs <;> e10om
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨6, by omega, ?_, chU_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HU, if_true, if_false]; e10om
      · show ¬ IU r s (0, 0); simp [IU]
      · simp only [cornZ, aU]; split_ifs <;> e10om
    · refine ⟨7, by omega, ?_, chU_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HU, if_true, if_false]; e10om
      · simp (config := {decide := true}) only [cornZ, IU]; e10om
      · simp only [cornZ, aU]; split_ifs <;> e10om
    · refine ⟨8, by omega, ?_, chU_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HU, if_true, if_false]; e10om
      · simp (config := {decide := true}) only [cornZ, IU]; e10om
      · simp only [cornZ, aU]; split_ifs <;> e10om
    · refine ⟨9, by omega, ?_, chU_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HU, if_true, if_false]; e10om
      · simp (config := {decide := true}) only [cornZ, IU]; e10om
      · simp only [cornZ, aU]; split_ifs <;> e10om
    · refine ⟨10, by omega, ?_, chU_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HU, if_true, if_false]; e10om
      · simp (config := {decide := true}) only [cornZ, IU]; e10om
      · simp only [cornZ, aU]; split_ifs <;> e10om
    · refine ⟨11, by omega, ?_, chU_bd ?_ ?_⟩
      · simp (config := {decide := true}) only [cornF, cornZ, QD, HU, if_true, if_false]; e10om
      · simp (config := {decide := true}) only [cornZ, IU]; e10om
      · simp only [cornZ, aU]; split_ifs <;> e10om

theorem qc_cap {f : ℕ} (hf : f < 2) : qc f = f := by unfold qc; split_ifs <;> omega

theorem qc_sec (c : ℕ) : qc (2 + c) = 2 := by unfold qc; split_ifs <;> omega

/-- **A chart point set of up to three points within two columns lies in one signature chart.** -/
theorem chart_set (H : Hyp p r s w) {c : ℕ} (hc : c < 3) (x0 : ℤ) (P : (ℤ × ℤ) → Prop)
    (hP : ∀ z, P z → Dom p r s c z ∧ (c = 2 → (z.1 = x0 ∨ z.1 = x0 + 1))) :
    ∃ f, f < 5 ∧ ∃ t : ℤ × ℤ, (c < 2 → t = 0) ∧ ∀ z, P z →
      QD p r s f (z + t) ∧ ch p r s w (qc f) (z + t) = ch p r s w c z := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
  · exact ⟨0, by omega, 0, fun _ => rfl, fun z hz => by simpa using ⟨(hP z hz).1, rfl⟩⟩
  · exact ⟨1, by omega, 0, fun _ => rfl, fun z hz => by simpa using ⟨(hP z hz).1, rfl⟩⟩
  · obtain ⟨t, c', hc', ht⟩ := tube_place (p := p) H.hr H.hs x0
    refine ⟨2 + c', by omega, t • per r s, fun h => by omega, fun z hz => ?_⟩
    have := hP z hz
    refine ⟨ht z this.1 (this.2 rfl), ?_⟩
    rw [qc_sec, chT_shift]

/-- **Edges in one chart.** -/
theorem chart_pair (H : Hyp p r s w) {c : ℕ} (hc : c < 3) {z u : ℤ × ℤ} (h1 : Dom p r s c z)
    (h2 : Dom p r s c (z + u)) (hu : u ∈ unitVec) :
    ∃ f, f < 5 ∧ ∃ y, QD p r s f y ∧ QD p r s f (y + u) ∧ ch p r s w (qc f) y = ch p r s w c z ∧
      ch p r s w (qc f) (y + u) = ch p r s w c (z + u) := by
  have hu' := unit_small hu
  obtain ⟨f, hf, t, -, ht⟩ := chart_set H hc (min z.1 (z.1 + u.1)) (fun x => x = z ∨ x = z + u)
    (by
      rintro x (rfl | rfl)
      · exact ⟨h1, fun _ => by omega⟩
      · exact ⟨h2, fun _ => by simp only [Prod.fst_add]; omega⟩)
  obtain ⟨a1, a2⟩ := ht z (Or.inl rfl)
  obtain ⟨b1, b2⟩ := ht (z + u) (Or.inr rfl)
  refine ⟨f, hf, z + t, a1, ?_, a2, ?_⟩
  · rwa [show z + t + u = z + u + t by abel]
  · rwa [show z + t + u = z + u + t by abel]

/-- **Triangles in one chart.** -/
theorem chart_tri (H : Hyp p r s w) {c : ℕ} (hc : c < 3) {a b e : ℤ × ℤ} (ha : Dom p r s c a)
    (hb : Dom p r s c b) (he : Dom p r s c e) (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec)
    (u3 : e - b ∈ unitVec) :
    ∃ f, f < 5 ∧ ∃ t : ℤ × ℤ, QD p r s f (a + t) ∧ QD p r s f (b + t) ∧ QD p r s f (e + t) ∧
      ch p r s w (qc f) (a + t) = ch p r s w c a ∧ ch p r s w (qc f) (b + t) = ch p r s w c b ∧
      ch p r s w (qc f) (e + t) = ch p r s w c e := by
  have v1 := unit_small u1; have v2 := unit_small u2; have v3 := unit_small u3
  simp only [Prod.fst_sub] at v1 v2 v3
  obtain ⟨f, hf, t, -, ht⟩ := chart_set H hc (min a.1 (min b.1 e.1)) (fun x => x = a ∨ x = b ∨ x = e)
    (by
      rintro x (rfl | rfl | rfl)
      · exact ⟨ha, fun _ => by omega⟩
      · exact ⟨hb, fun _ => by omega⟩
      · exact ⟨he, fun _ => by omega⟩)
  obtain ⟨a1, a2⟩ := ht a (Or.inl rfl)
  obtain ⟨b1, b2⟩ := ht b (Or.inr (Or.inl rfl))
  obtain ⟨e1, e2⟩ := ht e (Or.inr (Or.inr rfl))
  exact ⟨f, hf, t, a1, b1, e1, a2, b2, e2⟩

end Claude5E10
