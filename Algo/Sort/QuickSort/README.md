# Dafny 快速排序实现

（按：本文由 Gemini 2.5 Pro 生成。）

本仓库包含一个使用 Dafny 语言实现的快速排序算法，并附有完整的形式化证明。

`quicksort.dfy` 文件主要包含以下内容：

*   **`QuickSort(a: array<int>)`**: 对整数数组进行排序的主方法。
*   **`QuickSortAux(a: array<int>, l: nat, r: nat)`**: 实现递归排序的核心辅助方法。
*   **`Partition(a: array<int>, l: nat, r: nat)`**: 经典的划分方法，它将数组的一部分重新排列，并以一个主元（pivot）为界，分为两个子数组。
*   **引理（Lemmas）和幽灵谓词（Ghost Predicates）**: 一系列用于辅助证明的逻辑断言，例如：
    *   `Sorted(a: seq<int>)`: 验证序列是否有序。
    *   `multiset(a[l..r]) == old(multiset(a[l..r]))`: 确保排序过程不会改变数组元素的多重集，即元素本身和它们的数量都保持不变，仅仅改变顺序。

该实现通过 Dafny 的验证器证明了算法的两个关键属性：

1.  **排序正确性**: 输出数组是完全有序的。
2.  **数据保持性**: 输出数组是输入数组的一个排列。
