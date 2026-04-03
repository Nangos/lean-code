# LeanCode: Formally Verified LeetCode 

This project showcases formally verified implementations of LeetCode problems using the **Lean 4** proof assistant. Unlike traditional solutions, each algorithm here includes a rigorous proof of correctness and termination integrated directly into the code using dependent types.

## Highlights
* **Verified Correctness:** Every solution is guaranteed to satisfy the problem's specifications.
* **Performance:** Uses Lean's efficient built-in data structures (e.g., `Std.Data.HashMap`) to maintain optimal asymptotic complexity.
* **Executable:** All verified functions are fully computable and benchmarked.

The initial module, `P0001_TwoSum.lean`, provides a verified $O(n)$ hash map approach to the classic Two Sum problem, demonstrating a high-performance solution that is both mathematically sound and industry-speed ready.

---

## Getting Started
To run the performance tests:
```bash
lake exe perf_test
```
