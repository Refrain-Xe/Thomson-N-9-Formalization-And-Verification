import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSliceM3

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_m3 : checkKronCapAtT (wForT (-3 : ℤ)) (-3 : ℤ) = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSliceM3
