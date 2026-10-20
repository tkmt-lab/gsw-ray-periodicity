import Formal.Claude2K3Local

/-!
# K3 aligned surface: the two triangles on an edge

Written by a Claude worker (2026-10-19, K3 necessity session).  Generated in part by
`studies/R002/claude-lean/claude2_k3_gen_apex.py`.

For a unit segment `b → b + u` of a cell `c`, `apex_left` gives a cell `f` and a gluing
`gmap m τ` (identity if the left apex `b + rot u` lies in `c`) such that the images of `b`,
`b + u`, `b + rot u` lie in `f`, represent the same vertices, and the left apex is a different
vertex from the right apex `b + u - rot u` (when the latter lies in `c`).  The translation `τ` is
an integer combination of `r` and `s` (`InSpan`), which is what the necessity argument uses.
-/

set_option linter.unusedSimpArgs false

namespace Claude2K3
open ClaudeChallenge Claude2Aligned
variable {r s : ℤ}

/-- Integer combinations of `r` and `s`. -/
def InSpan (r s : ℤ) (τ : ℤ × ℤ) : Prop := ∃ a b c d : ℤ, τ = (a * r + b * s, c * r + d * s)

/-- The shift table of the necessity invariant: in cell `c`, for walk direction `d`, the odd-side
cross product is `±1 + k s (mod r)` with `k ∈ {0, ks c d}` (computed as the closure of the corner
values under all gluings, by `claude2_k3_gen_apex.py`). -/
def ks (c : Fin 11) (d : ℤ × ℤ) : ℤ :=
  if c.val < 3 then (if d = (-1, 1) then 1 else if d = (1, -1) then -1 else 0)
  else if c.val = 3 ∨ c.val = 7 then 0
  else if c.val < 7 then (if d = (1, 0) then 1 else if d = (-1, 0) then -1 else 0)
  else (if d = (1, 0) ∨ d = (0, 1) then 1 else if d = (-1, 0) ∨ d = (0, -1) then -1 else 0)

/-- The left apex of `b → b + u` (cell `c`), read in a cell `f` through a gluing. -/
def ApexData (r s : ℤ) (c : Fin 11) (b u : ℤ × ℤ) : Prop :=
  ∃ (f : Fin 11) (m : ℕ) (τ : ℤ × ℤ), InSpan r s τ ∧
    CellIn r s f (gmap m τ b) ∧ CellIn r s f (gmap m τ (b + u)) ∧
    CellIn r s f (gmap m τ (b + rot u)) ∧
    V r s c b = V r s f (gmap m τ b) ∧ V r s c (b + u) = V r s f (gmap m τ (b + u)) ∧
    (CellIn r s c (b + u - rot u) → V r s f (gmap m τ (b + rot u)) ≠ V r s c (b + u - rot u)) ∧
    (CellIn r s c (b + rot u) → V r s f (gmap m τ (b + rot u)) = V r s c (b + rot u)) ∧
    (∀ d, d = rot u ∨ d = rot u - u → ∀ k, k = 0 ∨ k = ks c d →
      ∃ k', (k' = 0 ∨ k' = ks f (rotN m d)) ∧ r ∣ cross (rotN m d) τ + k * s - k' * s)

theorem gmap_zero (z : ℤ × ℤ) : gmap 0 0 z = z := by simp [gmap, rotN]

theorem rot_ne_sub {b u : ℤ × ℤ} (hu : u ∈ unitVec) : b + rot u ≠ b + u - rot u := by
  intro h
  have h' : rot u = u - rot u := by
    have := congrArg (fun z => z - b) h; simpa [add_sub_assoc] using this
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rot, Prod.ext_iff] at h' <;> omega

theorem apex_same (hr : 0 < r) (hs : 0 < s) {c : Fin 11} {b u : ℤ × ℤ} (hu : u ∈ unitVec)
    (hb : CellIn r s c b) (he : CellIn r s c (b + u)) (hin : CellIn r s c (b + rot u)) :
    ApexData r s c b u := by
  refine ⟨c, 0, 0, ⟨0, 0, 0, 0, by ext <;> simp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [gmap_zero]
  · exact hb
  · exact he
  · exact hin
  · intro h; exact V_ne_cell hr hs hin h (rot_ne_sub hu)
  · exact fun _ => trivial
  · intro d _ k hk
    exact ⟨k, hk, by simp [cross]⟩

theorem apex_glue (hr : 0 < r) (hs : 0 < s) {c f : Fin 11} {i j m : ℕ} {τ : ℤ × ℤ}
    (hG : (k3Sig r s).Glue c i f j m τ) (hτ : InSpan r s τ) {b u : ℤ × ℤ}
    (hb : CellIn r s c b) (he : CellIn r s c (b + u)) (hout : ¬ CellIn r s c (b + rot u))
    (h1 : CellIn r s f (gmap m τ b)) (h2 : CellIn r s f (gmap m τ (b + u)))
    (h3 : CellIn r s f (gmap m τ (b + rot u)))
    (hne : CellIn r s c (b + u - rot u) →
      inv3 r s (f, gmap m τ (b + rot u)) ≠ inv3 r s (c, b + u - rot u))
    (hk : ∀ d, d = rot u ∨ d = rot u - u → ∀ k, k = 0 ∨ k = ks c d →
      ∃ k', (k' = 0 ∨ k' = ks f (rotN m d)) ∧ r ∣ cross (rotN m d) τ + k * s - k' * s) :
    ApexData r s c b u :=
  ⟨f, m, τ, hτ, h1, h2, h3, V_glue hr hs hG rfl hb h1, V_glue hr hs hG rfl he h2,
    fun h => V_ne3 hr hs h3 h (hne h), fun h => absurd h hout, hk⟩

macro "ap_tac" : tactic =>
  `(tactic| (simp [CellIn, TriIn, HexIn, gmap, rotN, rot] at * <;> omega))

macro "apne_tac" : tactic =>
  `(tactic| (
      intro h
      simp [CellIn, TriIn, HexIn, gmap, rotN, rot] at *
      simp [inv3, inv, hgt, ang, nrm, aux, gmap, rotN, rot, Prod.ext_iff]
      (try split_ifs) <;> omega))

set_option maxHeartbeats 8000000 in
/-- **The left triangle on a unit segment of a cell.** -/
theorem apex_left (hr : 2 ≤ r) (hs : 2 ≤ s) (c : Fin 11) (b u : ℤ × ℤ) (hu : u ∈ unitVec)
    (hb : CellIn r s c b) (he : CellIn r s c (b + u)) : ApexData r s c b u := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  by_cases hin : CellIn r s c (b + rot u)
  · exact apex_same hr0 hs0 hu hb he hin
  obtain ⟨x, y⟩ := b
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hu
  fin_cases c <;> rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_0_2 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_0_0 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_0_1 (r := r) (s := s)) ⟨-1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_1_2 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_1_0 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_1_1 (r := r) (s := s)) ⟨1, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_2_2 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_2_0 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_2_1 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_3_2 (r := r) (s := s)) ⟨1, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_3_0 (r := r) (s := s)) ⟨0, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_3_1 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_4_2 (r := r) (s := s)) ⟨0, -1, 1, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_4_0 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_4_1 (r := r) (s := s)) ⟨0, -1, 2, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_5_2 (r := r) (s := s)) ⟨0, -1, 1, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_5_0 (r := r) (s := s)) ⟨0, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_5_1 (r := r) (s := s)) ⟨0, -1, 2, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_6_2 (r := r) (s := s)) ⟨0, -1, 1, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_6_0 (r := r) (s := s)) ⟨1, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_6_1 (r := r) (s := s)) ⟨0, -1, 2, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_7_2 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_7_0 (r := r) (s := s)) ⟨1, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · exfalso; simp [CellIn, TriIn, HexIn, rot] at hb he hin; omega
  · refine apex_glue hr0 hs0 (gl_7_1 (r := r) (s := s)) ⟨1, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_8_3 (r := r) (s := s)) ⟨2, 0, 0, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_8_4 (r := r) (s := s)) ⟨0, -1, 1, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_8_5 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_8_0 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_8_1 (r := r) (s := s)) ⟨2, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_8_2 (r := r) (s := s)) ⟨-1, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_9_3 (r := r) (s := s)) ⟨2, 0, 0, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_9_4 (r := r) (s := s)) ⟨0, -1, 1, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_9_5 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_9_0 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_9_1 (r := r) (s := s)) ⟨2, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_9_2 (r := r) (s := s)) ⟨-1, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_10_3 (r := r) (s := s)) ⟨2, 0, 0, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 2, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_10_4 (r := r) (s := s)) ⟨0, -1, 1, 1, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_10_5 (r := r) (s := s)) ⟨1, 0, 1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_10_0 (r := r) (s := s)) ⟨0, 0, 0, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨-1, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 0, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_10_1 (r := r) (s := s)) ⟨2, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -2, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
  · refine apex_glue hr0 hs0 (gl_10_2 (r := r) (s := s)) ⟨-1, 0, -1, 0, by ext <;> simp⟩
      hb he hin (by ap_tac) (by ap_tac) (by ap_tac) (by apne_tac) ?_
    intro d hd k hk
    rcases hd with rfl | rfl <;> rcases hk with rfl | rfl
    · exact ⟨0, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], -1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨0, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩
    · exact ⟨1, by simp [ks, rot, rotN], 1, by simp [cross, rotN, rot, ks] <;> ring⟩

/-- One of the two apexes of a unit segment of a cell lies in the cell. -/
theorem apex_some_in (hr : 2 ≤ r) (hs : 2 ≤ s) (c : Fin 11) (b u : ℤ × ℤ) (hu : u ∈ unitVec)
    (hb : CellIn r s c b) (he : CellIn r s c (b + u)) :
    CellIn r s c (b + rot u) ∨ CellIn r s c (b + u - rot u) := by
  obtain ⟨x, y⟩ := b
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hu
  fin_cases c <;> rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CellIn, TriIn, HexIn, rot] at hb he ⊢ <;> omega

end Claude2K3

#print axioms Claude2K3.apex_left
#print axioms Claude2K3.apex_some_in
