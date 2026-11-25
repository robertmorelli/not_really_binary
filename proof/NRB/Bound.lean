import NRB.Ranges.R0
import NRB.Ranges.R1
import NRB.Ranges.R2
import NRB.Ranges.R3
import NRB.Ranges.R4
import NRB.Ranges.R5
import NRB.Ranges.R6
import NRB.Ranges.R7
import NRB.Ranges.R8
import NRB.Ranges.R9
import NRB.Ranges.R10
import NRB.Ranges.R11
import NRB.Ranges.R12
import NRB.Ranges.R13
import NRB.Ranges.R14
import NRB.Ranges.R15

/-- No solution has between 3000 and 17179872184 base-6 digits. -/
theorem cover_all : cover 3000 17179872184 := cover_trans r0 (cover_trans r1 (cover_trans r2 (cover_trans r3 (cover_trans r4 (cover_trans r5 (cover_trans r6 (cover_trans r7 (cover_trans r8 (cover_trans r9 (cover_trans r10 (cover_trans r11 (cover_trans r12 (cover_trans r13 (cover_trans r14 (r15)))))))))))))))

/-- Verified lower bound: a(6), if it exists, is at least 6^17179872184. -/
theorem a6_bound : ∀ N, 1 < N → N < 6 ^ 17179872184 → good 6 N = false :=
  below_of_cover cover_all

#print axioms a6_bound
