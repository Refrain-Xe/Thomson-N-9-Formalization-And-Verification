import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSliceM4

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_m4 : checkKronCapAtT (wForT (-4 : ℤ)) (-4 : ℤ) = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSliceM4
