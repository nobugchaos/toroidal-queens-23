import ToroidalQueens23.Lift

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace ToroidalQueens23
noncomputable section

@[simp] theorem exponent_inj (a b i j : Nat) :
    exponent a b = exponent i j ↔ a = i ∧ b = j := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun d => d 0) h,
      by simpa using congrArg (fun d => d 1) h⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem term_monomial (c : F) (a b : Nat) :
    MvPolynomial.C c * px^a * py^b = MvPolynomial.monomial (exponent a b) c := by
  simp [px,py,MvPolynomial.X_pow_eq_monomial,MvPolynomial.C_mul_monomial,exponent]

@[simp] theorem coeff_term (c : F) (a b i j : Nat) :
    (MvPolynomial.C c * px^a * py^b).coeff (exponent i j) =
      if a = i ∧ b = j then c else 0 := by
  rw [term_monomial,MvPolynomial.coeff_monomial]
  simp [eq_comm,exponent_inj]

def topKernel : Poly := px^11*py^11*ps^11*pd^11

theorem topKernel_expansion : topKernel =
    MvPolynomial.C ((1 : Int) : F)*px^33*py^11+
    MvPolynomial.C ((-11 : Int) : F)*px^31*py^13+
    MvPolynomial.C ((55 : Int) : F)*px^29*py^15+
    MvPolynomial.C ((-165 : Int) : F)*px^27*py^17+
    MvPolynomial.C ((330 : Int) : F)*px^25*py^19+
    MvPolynomial.C ((-462 : Int) : F)*px^23*py^21+
    MvPolynomial.C ((462 : Int) : F)*px^21*py^23+
    MvPolynomial.C ((-330 : Int) : F)*px^19*py^25+
    MvPolynomial.C ((165 : Int) : F)*px^17*py^27+
    MvPolynomial.C ((-55 : Int) : F)*px^15*py^29+
    MvPolynomial.C ((11 : Int) : F)*px^13*py^31+
    MvPolynomial.C ((-1 : Int) : F)*px^11*py^33 := by
  simp only [topKernel,ps,pd,map_intCast]
  ring

theorem topKernel_high_zero (i j : Nat) (h : i+j < 44) :
    topKernel.coeff (exponent i j) = 0 := by
  rw [topKernel_expansion]
  have hn0 : ¬ (33 = i ∧ 11 = j) := by omega
  have hn1 : ¬ (31 = i ∧ 13 = j) := by omega
  have hn2 : ¬ (29 = i ∧ 15 = j) := by omega
  have hn3 : ¬ (27 = i ∧ 17 = j) := by omega
  have hn4 : ¬ (25 = i ∧ 19 = j) := by omega
  have hn5 : ¬ (23 = i ∧ 21 = j) := by omega
  have hn6 : ¬ (21 = i ∧ 23 = j) := by omega
  have hn7 : ¬ (19 = i ∧ 25 = j) := by omega
  have hn8 : ¬ (17 = i ∧ 27 = j) := by omega
  have hn9 : ¬ (15 = i ∧ 29 = j) := by omega
  have hn10 : ¬ (13 = i ∧ 31 = j) := by omega
  have hn11 : ¬ (11 = i ∧ 33 = j) := by omega
  simp only [MvPolynomial.coeff_add,coeff_term,if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7, if_neg hn8, if_neg hn9, if_neg hn10, if_neg hn11,add_zero]

def kernelR2 : Poly := px^9*py^11*ps^11*pd^11

theorem kernelR2_expansion : kernelR2 =
    MvPolynomial.C ((1 : Int) : F)*px^31*py^11+
    MvPolynomial.C ((-11 : Int) : F)*px^29*py^13+
    MvPolynomial.C ((55 : Int) : F)*px^27*py^15+
    MvPolynomial.C ((-165 : Int) : F)*px^25*py^17+
    MvPolynomial.C ((330 : Int) : F)*px^23*py^19+
    MvPolynomial.C ((-462 : Int) : F)*px^21*py^21+
    MvPolynomial.C ((462 : Int) : F)*px^19*py^23+
    MvPolynomial.C ((-330 : Int) : F)*px^17*py^25+
    MvPolynomial.C ((165 : Int) : F)*px^15*py^27+
    MvPolynomial.C ((-55 : Int) : F)*px^13*py^29+
    MvPolynomial.C ((11 : Int) : F)*px^11*py^31+
    MvPolynomial.C ((-1 : Int) : F)*px^9*py^33 := by
  simp only [kernelR2,ps,pd,map_intCast]
  ring

theorem kernelR2_coefficient (i j : Nat) :
    kernelR2.coeff (exponent i j) =
    (if 31 = i ∧ 11 = j then ((1:Int):F) else 0)+
    (if 29 = i ∧ 13 = j then ((-11:Int):F) else 0)+
    (if 27 = i ∧ 15 = j then ((55:Int):F) else 0)+
    (if 25 = i ∧ 17 = j then ((-165:Int):F) else 0)+
    (if 23 = i ∧ 19 = j then ((330:Int):F) else 0)+
    (if 21 = i ∧ 21 = j then ((-462:Int):F) else 0)+
    (if 19 = i ∧ 23 = j then ((462:Int):F) else 0)+
    (if 17 = i ∧ 25 = j then ((-330:Int):F) else 0)+
    (if 15 = i ∧ 27 = j then ((165:Int):F) else 0)+
    (if 13 = i ∧ 29 = j then ((-55:Int):F) else 0)+
    (if 11 = i ∧ 31 = j then ((11:Int):F) else 0)+
    (if 9 = i ∧ 33 = j then ((-1:Int):F) else 0) := by
  rw [kernelR2_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def kernelC2 : Poly := px^11*py^9*ps^11*pd^11

theorem kernelC2_expansion : kernelC2 =
    MvPolynomial.C ((1 : Int) : F)*px^33*py^9+
    MvPolynomial.C ((-11 : Int) : F)*px^31*py^11+
    MvPolynomial.C ((55 : Int) : F)*px^29*py^13+
    MvPolynomial.C ((-165 : Int) : F)*px^27*py^15+
    MvPolynomial.C ((330 : Int) : F)*px^25*py^17+
    MvPolynomial.C ((-462 : Int) : F)*px^23*py^19+
    MvPolynomial.C ((462 : Int) : F)*px^21*py^21+
    MvPolynomial.C ((-330 : Int) : F)*px^19*py^23+
    MvPolynomial.C ((165 : Int) : F)*px^17*py^25+
    MvPolynomial.C ((-55 : Int) : F)*px^15*py^27+
    MvPolynomial.C ((11 : Int) : F)*px^13*py^29+
    MvPolynomial.C ((-1 : Int) : F)*px^11*py^31 := by
  simp only [kernelC2,ps,pd,map_intCast]
  ring

theorem kernelC2_coefficient (i j : Nat) :
    kernelC2.coeff (exponent i j) =
    (if 33 = i ∧ 9 = j then ((1:Int):F) else 0)+
    (if 31 = i ∧ 11 = j then ((-11:Int):F) else 0)+
    (if 29 = i ∧ 13 = j then ((55:Int):F) else 0)+
    (if 27 = i ∧ 15 = j then ((-165:Int):F) else 0)+
    (if 25 = i ∧ 17 = j then ((330:Int):F) else 0)+
    (if 23 = i ∧ 19 = j then ((-462:Int):F) else 0)+
    (if 21 = i ∧ 21 = j then ((462:Int):F) else 0)+
    (if 19 = i ∧ 23 = j then ((-330:Int):F) else 0)+
    (if 17 = i ∧ 25 = j then ((165:Int):F) else 0)+
    (if 15 = i ∧ 27 = j then ((-55:Int):F) else 0)+
    (if 13 = i ∧ 29 = j then ((11:Int):F) else 0)+
    (if 11 = i ∧ 31 = j then ((-1:Int):F) else 0) := by
  rw [kernelC2_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def kernelS2 : Poly := px^11*py^11*ps^9*pd^11

theorem kernelS2_expansion : kernelS2 =
    MvPolynomial.C ((1 : Int) : F)*px^31*py^11+
    MvPolynomial.C ((-2 : Int) : F)*px^30*py^12+
    MvPolynomial.C ((-8 : Int) : F)*px^29*py^13+
    MvPolynomial.C ((18 : Int) : F)*px^28*py^14+
    MvPolynomial.C ((27 : Int) : F)*px^27*py^15+
    MvPolynomial.C ((-72 : Int) : F)*px^26*py^16+
    MvPolynomial.C ((-48 : Int) : F)*px^25*py^17+
    MvPolynomial.C ((168 : Int) : F)*px^24*py^18+
    MvPolynomial.C ((42 : Int) : F)*px^23*py^19+
    MvPolynomial.C ((-252 : Int) : F)*px^22*py^20+
    MvPolynomial.C ((252 : Int) : F)*px^20*py^22+
    MvPolynomial.C ((-42 : Int) : F)*px^19*py^23+
    MvPolynomial.C ((-168 : Int) : F)*px^18*py^24+
    MvPolynomial.C ((48 : Int) : F)*px^17*py^25+
    MvPolynomial.C ((72 : Int) : F)*px^16*py^26+
    MvPolynomial.C ((-27 : Int) : F)*px^15*py^27+
    MvPolynomial.C ((-18 : Int) : F)*px^14*py^28+
    MvPolynomial.C ((8 : Int) : F)*px^13*py^29+
    MvPolynomial.C ((2 : Int) : F)*px^12*py^30+
    MvPolynomial.C ((-1 : Int) : F)*px^11*py^31 := by
  simp only [kernelS2,ps,pd,map_intCast]
  ring

theorem kernelS2_coefficient (i j : Nat) :
    kernelS2.coeff (exponent i j) =
    (if 31 = i ∧ 11 = j then ((1:Int):F) else 0)+
    (if 30 = i ∧ 12 = j then ((-2:Int):F) else 0)+
    (if 29 = i ∧ 13 = j then ((-8:Int):F) else 0)+
    (if 28 = i ∧ 14 = j then ((18:Int):F) else 0)+
    (if 27 = i ∧ 15 = j then ((27:Int):F) else 0)+
    (if 26 = i ∧ 16 = j then ((-72:Int):F) else 0)+
    (if 25 = i ∧ 17 = j then ((-48:Int):F) else 0)+
    (if 24 = i ∧ 18 = j then ((168:Int):F) else 0)+
    (if 23 = i ∧ 19 = j then ((42:Int):F) else 0)+
    (if 22 = i ∧ 20 = j then ((-252:Int):F) else 0)+
    (if 20 = i ∧ 22 = j then ((252:Int):F) else 0)+
    (if 19 = i ∧ 23 = j then ((-42:Int):F) else 0)+
    (if 18 = i ∧ 24 = j then ((-168:Int):F) else 0)+
    (if 17 = i ∧ 25 = j then ((48:Int):F) else 0)+
    (if 16 = i ∧ 26 = j then ((72:Int):F) else 0)+
    (if 15 = i ∧ 27 = j then ((-27:Int):F) else 0)+
    (if 14 = i ∧ 28 = j then ((-18:Int):F) else 0)+
    (if 13 = i ∧ 29 = j then ((8:Int):F) else 0)+
    (if 12 = i ∧ 30 = j then ((2:Int):F) else 0)+
    (if 11 = i ∧ 31 = j then ((-1:Int):F) else 0) := by
  rw [kernelS2_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def kernelD2 : Poly := px^11*py^11*ps^11*pd^9

theorem kernelD2_expansion : kernelD2 =
    MvPolynomial.C ((1 : Int) : F)*px^31*py^11+
    MvPolynomial.C ((2 : Int) : F)*px^30*py^12+
    MvPolynomial.C ((-8 : Int) : F)*px^29*py^13+
    MvPolynomial.C ((-18 : Int) : F)*px^28*py^14+
    MvPolynomial.C ((27 : Int) : F)*px^27*py^15+
    MvPolynomial.C ((72 : Int) : F)*px^26*py^16+
    MvPolynomial.C ((-48 : Int) : F)*px^25*py^17+
    MvPolynomial.C ((-168 : Int) : F)*px^24*py^18+
    MvPolynomial.C ((42 : Int) : F)*px^23*py^19+
    MvPolynomial.C ((252 : Int) : F)*px^22*py^20+
    MvPolynomial.C ((-252 : Int) : F)*px^20*py^22+
    MvPolynomial.C ((-42 : Int) : F)*px^19*py^23+
    MvPolynomial.C ((168 : Int) : F)*px^18*py^24+
    MvPolynomial.C ((48 : Int) : F)*px^17*py^25+
    MvPolynomial.C ((-72 : Int) : F)*px^16*py^26+
    MvPolynomial.C ((-27 : Int) : F)*px^15*py^27+
    MvPolynomial.C ((18 : Int) : F)*px^14*py^28+
    MvPolynomial.C ((8 : Int) : F)*px^13*py^29+
    MvPolynomial.C ((-2 : Int) : F)*px^12*py^30+
    MvPolynomial.C ((-1 : Int) : F)*px^11*py^31 := by
  simp only [kernelD2,ps,pd,map_intCast]
  ring

theorem kernelD2_coefficient (i j : Nat) :
    kernelD2.coeff (exponent i j) =
    (if 31 = i ∧ 11 = j then ((1:Int):F) else 0)+
    (if 30 = i ∧ 12 = j then ((2:Int):F) else 0)+
    (if 29 = i ∧ 13 = j then ((-8:Int):F) else 0)+
    (if 28 = i ∧ 14 = j then ((-18:Int):F) else 0)+
    (if 27 = i ∧ 15 = j then ((27:Int):F) else 0)+
    (if 26 = i ∧ 16 = j then ((72:Int):F) else 0)+
    (if 25 = i ∧ 17 = j then ((-48:Int):F) else 0)+
    (if 24 = i ∧ 18 = j then ((-168:Int):F) else 0)+
    (if 23 = i ∧ 19 = j then ((42:Int):F) else 0)+
    (if 22 = i ∧ 20 = j then ((252:Int):F) else 0)+
    (if 20 = i ∧ 22 = j then ((-252:Int):F) else 0)+
    (if 19 = i ∧ 23 = j then ((-42:Int):F) else 0)+
    (if 18 = i ∧ 24 = j then ((168:Int):F) else 0)+
    (if 17 = i ∧ 25 = j then ((48:Int):F) else 0)+
    (if 16 = i ∧ 26 = j then ((-72:Int):F) else 0)+
    (if 15 = i ∧ 27 = j then ((-27:Int):F) else 0)+
    (if 14 = i ∧ 28 = j then ((18:Int):F) else 0)+
    (if 13 = i ∧ 29 = j then ((8:Int):F) else 0)+
    (if 12 = i ∧ 30 = j then ((-2:Int):F) else 0)+
    (if 11 = i ∧ 31 = j then ((-1:Int):F) else 0) := by
  rw [kernelD2_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def kernelR3 : Poly := px^8*py^11*ps^11*pd^11

theorem kernelR3_expansion : kernelR3 =
    MvPolynomial.C ((1 : Int) : F)*px^30*py^11+
    MvPolynomial.C ((-11 : Int) : F)*px^28*py^13+
    MvPolynomial.C ((55 : Int) : F)*px^26*py^15+
    MvPolynomial.C ((-165 : Int) : F)*px^24*py^17+
    MvPolynomial.C ((330 : Int) : F)*px^22*py^19+
    MvPolynomial.C ((-462 : Int) : F)*px^20*py^21+
    MvPolynomial.C ((462 : Int) : F)*px^18*py^23+
    MvPolynomial.C ((-330 : Int) : F)*px^16*py^25+
    MvPolynomial.C ((165 : Int) : F)*px^14*py^27+
    MvPolynomial.C ((-55 : Int) : F)*px^12*py^29+
    MvPolynomial.C ((11 : Int) : F)*px^10*py^31+
    MvPolynomial.C ((-1 : Int) : F)*px^8*py^33 := by
  simp only [kernelR3,ps,pd,map_intCast]
  ring

theorem kernelR3_coefficient (i j : Nat) :
    kernelR3.coeff (exponent i j) =
    (if 30 = i ∧ 11 = j then ((1:Int):F) else 0)+
    (if 28 = i ∧ 13 = j then ((-11:Int):F) else 0)+
    (if 26 = i ∧ 15 = j then ((55:Int):F) else 0)+
    (if 24 = i ∧ 17 = j then ((-165:Int):F) else 0)+
    (if 22 = i ∧ 19 = j then ((330:Int):F) else 0)+
    (if 20 = i ∧ 21 = j then ((-462:Int):F) else 0)+
    (if 18 = i ∧ 23 = j then ((462:Int):F) else 0)+
    (if 16 = i ∧ 25 = j then ((-330:Int):F) else 0)+
    (if 14 = i ∧ 27 = j then ((165:Int):F) else 0)+
    (if 12 = i ∧ 29 = j then ((-55:Int):F) else 0)+
    (if 10 = i ∧ 31 = j then ((11:Int):F) else 0)+
    (if 8 = i ∧ 33 = j then ((-1:Int):F) else 0) := by
  rw [kernelR3_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def kernelC3 : Poly := px^11*py^8*ps^11*pd^11

theorem kernelC3_expansion : kernelC3 =
    MvPolynomial.C ((1 : Int) : F)*px^33*py^8+
    MvPolynomial.C ((-11 : Int) : F)*px^31*py^10+
    MvPolynomial.C ((55 : Int) : F)*px^29*py^12+
    MvPolynomial.C ((-165 : Int) : F)*px^27*py^14+
    MvPolynomial.C ((330 : Int) : F)*px^25*py^16+
    MvPolynomial.C ((-462 : Int) : F)*px^23*py^18+
    MvPolynomial.C ((462 : Int) : F)*px^21*py^20+
    MvPolynomial.C ((-330 : Int) : F)*px^19*py^22+
    MvPolynomial.C ((165 : Int) : F)*px^17*py^24+
    MvPolynomial.C ((-55 : Int) : F)*px^15*py^26+
    MvPolynomial.C ((11 : Int) : F)*px^13*py^28+
    MvPolynomial.C ((-1 : Int) : F)*px^11*py^30 := by
  simp only [kernelC3,ps,pd,map_intCast]
  ring

theorem kernelC3_coefficient (i j : Nat) :
    kernelC3.coeff (exponent i j) =
    (if 33 = i ∧ 8 = j then ((1:Int):F) else 0)+
    (if 31 = i ∧ 10 = j then ((-11:Int):F) else 0)+
    (if 29 = i ∧ 12 = j then ((55:Int):F) else 0)+
    (if 27 = i ∧ 14 = j then ((-165:Int):F) else 0)+
    (if 25 = i ∧ 16 = j then ((330:Int):F) else 0)+
    (if 23 = i ∧ 18 = j then ((-462:Int):F) else 0)+
    (if 21 = i ∧ 20 = j then ((462:Int):F) else 0)+
    (if 19 = i ∧ 22 = j then ((-330:Int):F) else 0)+
    (if 17 = i ∧ 24 = j then ((165:Int):F) else 0)+
    (if 15 = i ∧ 26 = j then ((-55:Int):F) else 0)+
    (if 13 = i ∧ 28 = j then ((11:Int):F) else 0)+
    (if 11 = i ∧ 30 = j then ((-1:Int):F) else 0) := by
  rw [kernelC3_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def kernelS3 : Poly := px^11*py^11*ps^8*pd^11

theorem kernelS3_expansion : kernelS3 =
    MvPolynomial.C ((1 : Int) : F)*px^30*py^11+
    MvPolynomial.C ((-3 : Int) : F)*px^29*py^12+
    MvPolynomial.C ((-5 : Int) : F)*px^28*py^13+
    MvPolynomial.C ((23 : Int) : F)*px^27*py^14+
    MvPolynomial.C ((4 : Int) : F)*px^26*py^15+
    MvPolynomial.C ((-76 : Int) : F)*px^25*py^16+
    MvPolynomial.C ((28 : Int) : F)*px^24*py^17+
    MvPolynomial.C ((140 : Int) : F)*px^23*py^18+
    MvPolynomial.C ((-98 : Int) : F)*px^22*py^19+
    MvPolynomial.C ((-154 : Int) : F)*px^21*py^20+
    MvPolynomial.C ((154 : Int) : F)*px^20*py^21+
    MvPolynomial.C ((98 : Int) : F)*px^19*py^22+
    MvPolynomial.C ((-140 : Int) : F)*px^18*py^23+
    MvPolynomial.C ((-28 : Int) : F)*px^17*py^24+
    MvPolynomial.C ((76 : Int) : F)*px^16*py^25+
    MvPolynomial.C ((-4 : Int) : F)*px^15*py^26+
    MvPolynomial.C ((-23 : Int) : F)*px^14*py^27+
    MvPolynomial.C ((5 : Int) : F)*px^13*py^28+
    MvPolynomial.C ((3 : Int) : F)*px^12*py^29+
    MvPolynomial.C ((-1 : Int) : F)*px^11*py^30 := by
  simp only [kernelS3,ps,pd,map_intCast]
  ring

theorem kernelS3_coefficient (i j : Nat) :
    kernelS3.coeff (exponent i j) =
    (if 30 = i ∧ 11 = j then ((1:Int):F) else 0)+
    (if 29 = i ∧ 12 = j then ((-3:Int):F) else 0)+
    (if 28 = i ∧ 13 = j then ((-5:Int):F) else 0)+
    (if 27 = i ∧ 14 = j then ((23:Int):F) else 0)+
    (if 26 = i ∧ 15 = j then ((4:Int):F) else 0)+
    (if 25 = i ∧ 16 = j then ((-76:Int):F) else 0)+
    (if 24 = i ∧ 17 = j then ((28:Int):F) else 0)+
    (if 23 = i ∧ 18 = j then ((140:Int):F) else 0)+
    (if 22 = i ∧ 19 = j then ((-98:Int):F) else 0)+
    (if 21 = i ∧ 20 = j then ((-154:Int):F) else 0)+
    (if 20 = i ∧ 21 = j then ((154:Int):F) else 0)+
    (if 19 = i ∧ 22 = j then ((98:Int):F) else 0)+
    (if 18 = i ∧ 23 = j then ((-140:Int):F) else 0)+
    (if 17 = i ∧ 24 = j then ((-28:Int):F) else 0)+
    (if 16 = i ∧ 25 = j then ((76:Int):F) else 0)+
    (if 15 = i ∧ 26 = j then ((-4:Int):F) else 0)+
    (if 14 = i ∧ 27 = j then ((-23:Int):F) else 0)+
    (if 13 = i ∧ 28 = j then ((5:Int):F) else 0)+
    (if 12 = i ∧ 29 = j then ((3:Int):F) else 0)+
    (if 11 = i ∧ 30 = j then ((-1:Int):F) else 0) := by
  rw [kernelS3_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def kernelD3 : Poly := px^11*py^11*ps^11*pd^8

theorem kernelD3_expansion : kernelD3 =
    MvPolynomial.C ((1 : Int) : F)*px^30*py^11+
    MvPolynomial.C ((3 : Int) : F)*px^29*py^12+
    MvPolynomial.C ((-5 : Int) : F)*px^28*py^13+
    MvPolynomial.C ((-23 : Int) : F)*px^27*py^14+
    MvPolynomial.C ((4 : Int) : F)*px^26*py^15+
    MvPolynomial.C ((76 : Int) : F)*px^25*py^16+
    MvPolynomial.C ((28 : Int) : F)*px^24*py^17+
    MvPolynomial.C ((-140 : Int) : F)*px^23*py^18+
    MvPolynomial.C ((-98 : Int) : F)*px^22*py^19+
    MvPolynomial.C ((154 : Int) : F)*px^21*py^20+
    MvPolynomial.C ((154 : Int) : F)*px^20*py^21+
    MvPolynomial.C ((-98 : Int) : F)*px^19*py^22+
    MvPolynomial.C ((-140 : Int) : F)*px^18*py^23+
    MvPolynomial.C ((28 : Int) : F)*px^17*py^24+
    MvPolynomial.C ((76 : Int) : F)*px^16*py^25+
    MvPolynomial.C ((4 : Int) : F)*px^15*py^26+
    MvPolynomial.C ((-23 : Int) : F)*px^14*py^27+
    MvPolynomial.C ((-5 : Int) : F)*px^13*py^28+
    MvPolynomial.C ((3 : Int) : F)*px^12*py^29+
    MvPolynomial.C ((1 : Int) : F)*px^11*py^30 := by
  simp only [kernelD3,ps,pd,map_intCast]
  ring

theorem kernelD3_coefficient (i j : Nat) :
    kernelD3.coeff (exponent i j) =
    (if 30 = i ∧ 11 = j then ((1:Int):F) else 0)+
    (if 29 = i ∧ 12 = j then ((3:Int):F) else 0)+
    (if 28 = i ∧ 13 = j then ((-5:Int):F) else 0)+
    (if 27 = i ∧ 14 = j then ((-23:Int):F) else 0)+
    (if 26 = i ∧ 15 = j then ((4:Int):F) else 0)+
    (if 25 = i ∧ 16 = j then ((76:Int):F) else 0)+
    (if 24 = i ∧ 17 = j then ((28:Int):F) else 0)+
    (if 23 = i ∧ 18 = j then ((-140:Int):F) else 0)+
    (if 22 = i ∧ 19 = j then ((-98:Int):F) else 0)+
    (if 21 = i ∧ 20 = j then ((154:Int):F) else 0)+
    (if 20 = i ∧ 21 = j then ((154:Int):F) else 0)+
    (if 19 = i ∧ 22 = j then ((-98:Int):F) else 0)+
    (if 18 = i ∧ 23 = j then ((-140:Int):F) else 0)+
    (if 17 = i ∧ 24 = j then ((28:Int):F) else 0)+
    (if 16 = i ∧ 25 = j then ((76:Int):F) else 0)+
    (if 15 = i ∧ 26 = j then ((4:Int):F) else 0)+
    (if 14 = i ∧ 27 = j then ((-23:Int):F) else 0)+
    (if 13 = i ∧ 28 = j then ((-5:Int):F) else 0)+
    (if 12 = i ∧ 29 = j then ((3:Int):F) else 0)+
    (if 11 = i ∧ 30 = j then ((1:Int):F) else 0) := by
  rw [kernelD3_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]

def diagonalKernel10 : Poly := px^0*py^0*ps^10*pd^10

theorem diagonalKernel10_expansion : diagonalKernel10 =
    MvPolynomial.C ((1 : Int) : F)*px^20*py^0+
    MvPolynomial.C ((-10 : Int) : F)*px^18*py^2+
    MvPolynomial.C ((45 : Int) : F)*px^16*py^4+
    MvPolynomial.C ((-120 : Int) : F)*px^14*py^6+
    MvPolynomial.C ((210 : Int) : F)*px^12*py^8+
    MvPolynomial.C ((-252 : Int) : F)*px^10*py^10+
    MvPolynomial.C ((210 : Int) : F)*px^8*py^12+
    MvPolynomial.C ((-120 : Int) : F)*px^6*py^14+
    MvPolynomial.C ((45 : Int) : F)*px^4*py^16+
    MvPolynomial.C ((-10 : Int) : F)*px^2*py^18+
    MvPolynomial.C ((1 : Int) : F)*px^0*py^20 := by
  simp only [diagonalKernel10,ps,pd,map_intCast]
  ring

theorem diagonalKernel10_coefficient : diagonalKernel10.coeff (exponent 10 10) = 1 := by
  rw [diagonalKernel10_expansion]
  simp only [MvPolynomial.coeff_add,coeff_term]
  norm_num
  decide

end
end ToroidalQueens23
