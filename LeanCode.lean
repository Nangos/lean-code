-- Essentially a list of finished LeanCode problems.

import LeanCode.G00.P0001_TwoSum

-- Performance test!
def main : IO Unit := do
  TwoSum.performanceTest    100_000
  TwoSum.performanceTest  1_000_000
  TwoSum.performanceTest 10_000_000
