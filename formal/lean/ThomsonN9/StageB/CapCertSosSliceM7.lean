import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSliceM7

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_m7 : checkKronCapAtT (wForT (-7 : ℤ)) (-7 : ℤ) = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSliceM7
