import FailureOfSemipositiveMetricExtension.CentralTransverseLineSectionVanishing

/-! Direct representative-independent coverage of a dense candidate locus by
actual strict transforms of lines through the fourth centre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set

def GoodVector (w : Fin 3 → ℂ) : Prop := w 0 ≠ 0 ∧ w 1 ≠ 0 ∧ w 1-w 0 ≠ 0

def dataOfVector (w : Fin 3 → ℂ) (hw : GoodVector w) : Data where
  slope := w 1 / w 0
  slope_ne_zero := div_ne_zero hw.2.1 hw.1
  sub_ne_zero := by
    intro h
    apply hw.2.2
    have h' : w 1 / w 0 = 1 := sub_eq_zero.mp h
    exact sub_eq_zero.mpr ((div_eq_one_iff_eq hw.1).mp h')

theorem goodVector_ne_zero (w : Fin 3 → ℂ) (hw : GoodVector w) : w ≠ 0 := by
  intro h
  exact hw.1 (congrFun h 0)

theorem goodVector_xz_ne_zero (w : Fin 3 → ℂ) (hw : GoodVector w) :
    (![w 0,w 2] : Blowup.Plane) ≠ 0 := by
  intro h
  exact hw.1 (congrFun h 0)

theorem dataOfVector_baseVector (w : Fin 3 → ℂ) (hw : GoodVector w) :
    baseVector (dataOfVector w hw) ![w 0,w 2] = w := by
  ext j
  fin_cases j <;> simp [baseVector,dataOfVector,hw.1]

theorem dataOfVector_base (w : Fin 3 → ℂ) (hw : GoodVector w) :
    base (dataOfVector w hw)
      (Projectivization.mk ℂ ![w 0,w 2] (goodVector_xz_ne_zero w hw)) =
      Projectivization.mk ℂ w (goodVector_ne_zero w hw) := by
  rw [base_mk]
  congr 1
  exact dataOfVector_baseVector w hw

theorem goodVector_away_centre (w : Fin 3 → ℂ) (hw : GoodVector w) (r : Fin 4) :
    Projectivization.mk ℂ w (goodVector_ne_zero w hw) ≠ centre r 0 := by
  intro h
  rw [← centre_mk] at h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  fin_cases r
  · exact hw.2.1 (by simpa [centreVector,Coordinates.p₁] using h1.symm)
  · exact hw.1 (by simpa [centreVector,Coordinates.p₂] using h0.symm)
  · apply hw.2.2
    have hw0 : a = w 0 := by simpa [centreVector,Coordinates.p₃] using h0
    have hw1 : a = w 1 := by simpa [centreVector,Coordinates.p₃] using h1
    exact sub_eq_zero.mpr (hw1.symm.trans hw0)
  · exact hw.1 (by simpa [centreVector,Coordinates.p₄] using h0.symm)

theorem param_dataOfVector (p : Fiber 0) (w : Fin 3 → ℂ) (hw : GoodVector w)
    (hp : FixedFiber.blowdown 0 p = Projectivization.mk ℂ w (goodVector_ne_zero w hw)) :
    param (dataOfVector w hw)
      (Projectivization.mk ℂ ![w 0,w 2] (goodVector_xz_ne_zero w hw)) = p := by
  let q := param (dataOfVector w hw)
    (Projectivization.mk ℂ ![w 0,w 2] (goodVector_xz_ne_zero w hw))
  have hb : FixedFiber.blowdown 0 q = FixedFiber.blowdown 0 p :=
    (dataOfVector_base w hw).trans hp.symm
  apply Subtype.ext
  apply Prod.ext
  · exact hb
  · funext r
    apply directions_eq_away (FixedFiber.inclusion 0 q) (FixedFiber.inclusion 0 p) r hb rfl
    change FixedFiber.blowdown 0 q ≠ centre r 0
    rw [hb,hp]
    exact goodVector_away_centre w hw r

def genericLocus : Set (Fiber 0) :=
  {p | ∃ w : Fin 3 → ℂ, ∃ hw : GoodVector w,
    FixedFiber.blowdown 0 p = Projectivization.mk ℂ w (goodVector_ne_zero w hw)}

theorem genericLocus_mem_line (p : Fiber 0) (hp : p ∈ genericLocus) :
    ∃ c : Data, ∃ d : Direction, param c d = p := by
  obtain ⟨w,hw,hp⟩ := hp
  exact ⟨dataOfVector w hw,Projectivization.mk ℂ ![w 0,w 2] (goodVector_xz_ne_zero w hw),
    param_dataOfVector p w hw hp⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
