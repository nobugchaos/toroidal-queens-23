import ToroidalQueens23.Expansion
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace ToroidalQueens23
noncomputable section

@[simp] theorem kernelR2_22_20 : kernelR2.coeff (exponent 22 20) = (0 : F) := by
  rw [kernelR2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR2_21_21 : kernelR2.coeff (exponent 21 21) = (21 : F) := by
  rw [kernelR2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR2_20_22 : kernelR2.coeff (exponent 20 22) = (0 : F) := by
  rw [kernelR2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR2_22_19 : kernelR2.coeff (exponent 22 19) = (0 : F) := by
  rw [kernelR2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR2_21_20 : kernelR2.coeff (exponent 21 20) = (0 : F) := by
  rw [kernelR2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR2_20_21 : kernelR2.coeff (exponent 20 21) = (0 : F) := by
  rw [kernelR2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR2_19_22 : kernelR2.coeff (exponent 19 22) = (0 : F) := by
  rw [kernelR2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC2_22_20 : kernelC2.coeff (exponent 22 20) = (0 : F) := by
  rw [kernelC2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC2_21_21 : kernelC2.coeff (exponent 21 21) = (2 : F) := by
  rw [kernelC2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC2_20_22 : kernelC2.coeff (exponent 20 22) = (0 : F) := by
  rw [kernelC2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC2_22_19 : kernelC2.coeff (exponent 22 19) = (0 : F) := by
  rw [kernelC2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC2_21_20 : kernelC2.coeff (exponent 21 20) = (0 : F) := by
  rw [kernelC2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC2_20_21 : kernelC2.coeff (exponent 20 21) = (0 : F) := by
  rw [kernelC2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC2_19_22 : kernelC2.coeff (exponent 19 22) = (0 : F) := by
  rw [kernelC2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS2_22_20 : kernelS2.coeff (exponent 22 20) = (1 : F) := by
  rw [kernelS2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS2_21_21 : kernelS2.coeff (exponent 21 21) = (0 : F) := by
  rw [kernelS2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS2_20_22 : kernelS2.coeff (exponent 20 22) = (22 : F) := by
  rw [kernelS2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS2_22_19 : kernelS2.coeff (exponent 22 19) = (0 : F) := by
  rw [kernelS2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS2_21_20 : kernelS2.coeff (exponent 21 20) = (0 : F) := by
  rw [kernelS2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS2_20_21 : kernelS2.coeff (exponent 20 21) = (0 : F) := by
  rw [kernelS2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS2_19_22 : kernelS2.coeff (exponent 19 22) = (0 : F) := by
  rw [kernelS2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD2_22_20 : kernelD2.coeff (exponent 22 20) = (22 : F) := by
  rw [kernelD2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD2_21_21 : kernelD2.coeff (exponent 21 21) = (0 : F) := by
  rw [kernelD2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD2_20_22 : kernelD2.coeff (exponent 20 22) = (1 : F) := by
  rw [kernelD2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD2_22_19 : kernelD2.coeff (exponent 22 19) = (0 : F) := by
  rw [kernelD2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD2_21_20 : kernelD2.coeff (exponent 21 20) = (0 : F) := by
  rw [kernelD2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD2_20_21 : kernelD2.coeff (exponent 20 21) = (0 : F) := by
  rw [kernelD2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD2_19_22 : kernelD2.coeff (exponent 19 22) = (0 : F) := by
  rw [kernelD2_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR3_22_20 : kernelR3.coeff (exponent 22 20) = (0 : F) := by
  rw [kernelR3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR3_21_21 : kernelR3.coeff (exponent 21 21) = (0 : F) := by
  rw [kernelR3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR3_20_22 : kernelR3.coeff (exponent 20 22) = (0 : F) := by
  rw [kernelR3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR3_22_19 : kernelR3.coeff (exponent 22 19) = (8 : F) := by
  rw [kernelR3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR3_21_20 : kernelR3.coeff (exponent 21 20) = (0 : F) := by
  rw [kernelR3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR3_20_21 : kernelR3.coeff (exponent 20 21) = (21 : F) := by
  rw [kernelR3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelR3_19_22 : kernelR3.coeff (exponent 19 22) = (0 : F) := by
  rw [kernelR3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC3_22_20 : kernelC3.coeff (exponent 22 20) = (0 : F) := by
  rw [kernelC3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC3_21_21 : kernelC3.coeff (exponent 21 21) = (0 : F) := by
  rw [kernelC3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC3_20_22 : kernelC3.coeff (exponent 20 22) = (0 : F) := by
  rw [kernelC3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC3_22_19 : kernelC3.coeff (exponent 22 19) = (0 : F) := by
  rw [kernelC3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC3_21_20 : kernelC3.coeff (exponent 21 20) = (2 : F) := by
  rw [kernelC3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC3_20_21 : kernelC3.coeff (exponent 20 21) = (0 : F) := by
  rw [kernelC3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelC3_19_22 : kernelC3.coeff (exponent 19 22) = (15 : F) := by
  rw [kernelC3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS3_22_20 : kernelS3.coeff (exponent 22 20) = (0 : F) := by
  rw [kernelS3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS3_21_21 : kernelS3.coeff (exponent 21 21) = (0 : F) := by
  rw [kernelS3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS3_20_22 : kernelS3.coeff (exponent 20 22) = (0 : F) := by
  rw [kernelS3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS3_22_19 : kernelS3.coeff (exponent 22 19) = (17 : F) := by
  rw [kernelS3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS3_21_20 : kernelS3.coeff (exponent 21 20) = (7 : F) := by
  rw [kernelS3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS3_20_21 : kernelS3.coeff (exponent 20 21) = (16 : F) := by
  rw [kernelS3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelS3_19_22 : kernelS3.coeff (exponent 19 22) = (6 : F) := by
  rw [kernelS3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD3_22_20 : kernelD3.coeff (exponent 22 20) = (0 : F) := by
  rw [kernelD3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD3_21_21 : kernelD3.coeff (exponent 21 21) = (0 : F) := by
  rw [kernelD3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD3_20_22 : kernelD3.coeff (exponent 20 22) = (0 : F) := by
  rw [kernelD3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD3_22_19 : kernelD3.coeff (exponent 22 19) = (17 : F) := by
  rw [kernelD3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD3_21_20 : kernelD3.coeff (exponent 21 20) = (16 : F) := by
  rw [kernelD3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD3_20_21 : kernelD3.coeff (exponent 20 21) = (16 : F) := by
  rw [kernelD3_coefficient]
  norm_num <;> decide

@[simp] theorem kernelD3_19_22 : kernelD3.coeff (exponent 19 22) = (17 : F) := by
  rw [kernelD3_coefficient]
  norm_num <;> decide

theorem jet_degree {z e : Poly} (hz : z.totalDegree ≤ 1) (he : e.totalDegree ≤ 7)
    (u v : F) : (jet z u v e).totalDegree ≤ 11 := by
  exact degree_add_bound (degree_pow_bound hz 11) ((jetB_degree hz he u v).trans (by decide))

theorem jet_coeff_formula (uR uC uS uD vR vC vS vD : F) (eR eC eS eD : Poly)
    (heR : eR.totalDegree ≤ 7) (heC : eC.totalDegree ≤ 7)
    (heS : eS.totalDegree ≤ 7) (heD : eD.totalDegree ≤ 7) (i j : Nat) (hlo : 40 < i+j) (hhi : i+j < 44) :
    ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)).coeff (exponent i j) =
    uR*kernelR2.coeff (exponent i j)+
    uC*kernelC2.coeff (exponent i j)+
    uS*kernelS2.coeff (exponent i j)+
    uD*kernelD2.coeff (exponent i j)+
    vR*kernelR3.coeff (exponent i j)+
    vC*kernelC3.coeff (exponent i j)+
    vS*kernelS3.coeff (exponent i j)+
    vD*kernelD3.coeff (exponent i j) := by
  rw [jet_product_expansion]
  have he : (jetError uR uC uS uD vR vC vS vD eR eC eS eD).coeff (exponent i j) = 0 := by
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    have hb := jetError_degree uR uC uS uD vR vC vS vD eR eC eS eD heR heC heS heD
    change _ < (exponent i j).sum (fun _ n => n)
    rw [exponent_degree,exponent_zero,exponent_one]
    exact lt_of_le_of_lt hb hlo
  simp only [MvPolynomial.coeff_add,MvPolynomial.coeff_C_mul,
    topKernel_high_zero i j hhi,he,zero_add,add_zero]

theorem jet_equations (uR uC uS uD vR vC vS vD : F) (eR eC eS eD : Poly)
    (heR : eR.totalDegree ≤ 7) (heC : eC.totalDegree ≤ 7)
    (heS : eS.totalDegree ≤ 7) (heD : eD.totalDegree ≤ 7)
    (hz : ∀ x y : F, MvPolynomial.eval ![x,y] ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)) = 0) :
    uS+uD*22 = 0 ∧
    uR*21+uC*2 = 0 ∧
    vR*8+vS*17+vD*17 = 0 ∧
    vC*2+vS*7+vD*16 = 0 ∧
    vR*21+vS*16+vD*16 = 0 ∧
    vC*15+vS*6+vD*17 = 0 := by
  have hdeg : ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)).totalDegree ≤ 44 := by
    exact degree_four (jet_degree px_degree heR uR vR) (jet_degree py_degree heC uC vC)
      (jet_degree ps_degree heS uS vS) (jet_degree pd_degree heD uD vD)

  have h0 : uS+uD*22 = 0 := by
    have hc := high_coefficient_zero ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)) hdeg hz 22 20 (by decide) (by decide) (by decide)
    rw [jet_coeff_formula uR uC uS uD vR vC vS vD eR eC eS eD heR heC heS heD 22 20 (by decide) (by decide)] at hc
    simpa using hc
  have h1 : uR*21+uC*2 = 0 := by
    have hc := high_coefficient_zero ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)) hdeg hz 21 21 (by decide) (by decide) (by decide)
    rw [jet_coeff_formula uR uC uS uD vR vC vS vD eR eC eS eD heR heC heS heD 21 21 (by decide) (by decide)] at hc
    simpa using hc
  have h2 : vR*8+vS*17+vD*17 = 0 := by
    have hc := high_coefficient_zero ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)) hdeg hz 22 19 (by decide) (by decide) (by decide)
    rw [jet_coeff_formula uR uC uS uD vR vC vS vD eR eC eS eD heR heC heS heD 22 19 (by decide) (by decide)] at hc
    simpa using hc
  have h3 : vC*2+vS*7+vD*16 = 0 := by
    have hc := high_coefficient_zero ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)) hdeg hz 21 20 (by decide) (by decide) (by decide)
    rw [jet_coeff_formula uR uC uS uD vR vC vS vD eR eC eS eD heR heC heS heD 21 20 (by decide) (by decide)] at hc
    simpa using hc
  have h4 : vR*21+vS*16+vD*16 = 0 := by
    have hc := high_coefficient_zero ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)) hdeg hz 20 21 (by decide) (by decide) (by decide)
    rw [jet_coeff_formula uR uC uS uD vR vC vS vD eR eC eS eD heR heC heS heD 20 21 (by decide) (by decide)] at hc
    simpa using hc
  have h5 : vC*15+vS*6+vD*17 = 0 := by
    have hc := high_coefficient_zero ((jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD)) hdeg hz 19 22 (by decide) (by decide) (by decide)
    rw [jet_coeff_formula uR uC uS uD vR vC vS vD eR eC eS eD heR heC heS heD 19 22 (by decide) (by decide)] at hc
    simpa using hc
  exact ⟨h0,h1,h2,h3,h4,h5⟩

theorem solve_cubic_coefficients (vR vC vS vD : F)
    (h0 : vR*8+vS*17+vD*17 = 0)
    (h1 : vC*2+vS*7+vD*16 = 0)
    (h2 : vR*21+vS*16+vD*16 = 0)
    (h3 : vC*15+vS*6+vD*17 = 0) :
    vR = 0 ∧ vC = 0 ∧ vS = 0 ∧ vD = 0 := by
  have h00 : (254 : F) = 1 := by decide
  have h01 : (0 : F) = 0 := by decide
  have h02 : (368 : F) = 0 := by decide
  have h03 : (368 : F) = 0 := by decide
  have vR_id : vR = 16*(vR*8+vS*17+vD*17)+0*(vC*2+vS*7+vD*16)+6*(vR*21+vS*16+vD*16)+0*(vC*15+vS*6+vD*17) := by
    calc
      vR = 254*vR+0*vC+368*vS+368*vD := by simp only [h00,h01,h02,h03,zero_mul,one_mul,add_zero,zero_add]
      _ = 16*(vR*8+vS*17+vD*17)+0*(vC*2+vS*7+vD*16)+6*(vR*21+vS*16+vD*16)+0*(vC*15+vS*6+vD*17) := by ring
  have h10 : (0 : F) = 0 := by decide
  have h11 : (139 : F) = 1 := by decide
  have h12 : (161 : F) = 0 := by decide
  have h13 : (391 : F) = 0 := by decide
  have vC_id : vC = 0*(vR*8+vS*17+vD*17)+17*(vC*2+vS*7+vD*16)+0*(vR*21+vS*16+vD*16)+7*(vC*15+vS*6+vD*17) := by
    calc
      vC = 0*vR+139*vC+161*vS+391*vD := by simp only [h10,h11,h12,h13,zero_mul,one_mul,add_zero,zero_add]
      _ = 0*(vR*8+vS*17+vD*17)+17*(vC*2+vS*7+vD*16)+0*(vR*21+vS*16+vD*16)+7*(vC*15+vS*6+vD*17) := by ring
  have h20 : (92 : F) = 0 := by decide
  have h21 : (368 : F) = 0 := by decide
  have h22 : (346 : F) = 1 := by decide
  have h23 : (759 : F) = 0 := by decide
  have vS_id : vS = 1*(vR*8+vS*17+vD*17)+19*(vC*2+vS*7+vD*16)+4*(vR*21+vS*16+vD*16)+22*(vC*15+vS*6+vD*17) := by
    calc
      vS = 92*vR+368*vC+346*vS+759*vD := by simp only [h20,h21,h22,h23,zero_mul,one_mul,add_zero,zero_add]
      _ = 1*(vR*8+vS*17+vD*17)+19*(vC*2+vS*7+vD*16)+4*(vR*21+vS*16+vD*16)+22*(vC*15+vS*6+vD*17) := by ring
  have h30 : (92 : F) = 0 := by decide
  have h31 : (23 : F) = 0 := by decide
  have h32 : (115 : F) = 0 := by decide
  have h33 : (162 : F) = 1 := by decide
  have vD_id : vD = 1*(vR*8+vS*17+vD*17)+4*(vC*2+vS*7+vD*16)+4*(vR*21+vS*16+vD*16)+1*(vC*15+vS*6+vD*17) := by
    calc
      vD = 92*vR+23*vC+115*vS+162*vD := by simp only [h30,h31,h32,h33,zero_mul,one_mul,add_zero,zero_add]
      _ = 1*(vR*8+vS*17+vD*17)+4*(vC*2+vS*7+vD*16)+4*(vR*21+vS*16+vD*16)+1*(vC*15+vS*6+vD*17) := by ring
  exact ⟨by simpa [h0,h1,h2,h3] using vR_id,by simpa [h0,h1,h2,h3] using vC_id,
    by simpa [h0,h1,h2,h3] using vS_id,by simpa [h0,h1,h2,h3] using vD_id⟩

theorem solve_quadratic_coefficients (uR uC uS uD : F)
    (h0 : uS+uD*22 = 0) (h1 : uR*21+uC*2 = 0) : uR = uC ∧ uS = uD := by
  have h22 : (22 : F) = -1 := by decide
  have h21 : (21 : F) = -2 := by decide
  have h2 : (2 : F) ≠ 0 := by decide
  have hs : uS-uD = 0 := by simpa [h22,sub_eq_add_neg] using h0
  have hr : (uC-uR)*2 = 0 := by
    calc (uC-uR)*2 = uR*(-2)+uC*2 := by ring
         _ = 0 := by simpa [h21] using h1
  exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right h2)).symm,sub_eq_zero.mp hs⟩

end
end ToroidalQueens23
