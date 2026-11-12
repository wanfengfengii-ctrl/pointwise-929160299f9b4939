# intervalrules — 点态增量区间 Datalog 引擎（仅 Python 标准库）

面向供应链合规场景：基础关系以**半开整数区间 `[起点, 终点)`** 记录事实在
时间轴上的存在，更正（撤回/补录）按批次增量提交，引擎只沿受影响的元组和
区间传播，不做整关系重算、不做全局切片、不逐整数展开。

## 数据模型

- 每个关系的每个元组映射到一个稀疏的**分段常数计数函数**
  `[lo, hi, value]` 列表；`value > 0` 表示该时刻存在。
- 基础关系可被多条更改叠加；同批叠加后任一区间计数为负，或输入非法，则
  **整批回滚**，引擎状态不变，`apply` 返回 `{}`。
- 派生结果是逐时刻的**分层最小不动点**：允许正递归；递归关系按存在语义
  处理（重复证明只算存在）。撤回会移除失去全部外部支撑的环，仍有其他证明
  的元组保留。

## API

```python
from intervalrules import Engine

eng = Engine(
    base={"E": 2, "B": 2},                 # 关系名 -> 正整数元数
    rules=["R(X,Y) :- E(X,Y), !B(X,Y)"],  # 仅变量、合取、! 否定
)

net = eng.apply([
    ["E", ("a", "b"), 0, 5, 1],
    ["B", ("a", "b"), 2, 3, 1],
])
# net: {"R": [[("a","b"),0,2,1], [("a","b"),3,5,1]]}
eng.read("R")
# [ [("a","b"),0,2], [("a","b"),3,5] ]
```

- `apply(changes)`：每项为
  `[基础关系名, 字符串元组, 起点, 终点, 非零增量]`，要求 `起点 < 终点`。
  返回派生关系相对**批前**的净增删，条目为
  `[元组, 起点, 终点, ±1]`，按元组、起点排序并最大合并同号区间。
- `read(name)`：返回 `[元组, 起点, 终点]` 列表，同样排序并合并。

## 校验规则（构造期 `ValueError`）

未定义关系、元数冲突、否定变量或头变量未在正文字出现、基础关系作规则头、
负递归环（否定边落在递归 SCC 内）等一律拒绝。

## 增量算法要点

1. 非递归 SCC：对受影响规则分别计算**批前/批后两个世界的完整证明积**再做
   差，自连接天然正确；否定字面量在正不动点之后按所在世界求值。
2. 递归 SCC：先求受影响锥（affected cone）内的**指示函数最小不动点**
   （有限域上必然收敛，无外部支撑的环自动消失），再在固定支撑上确定区间。
3. 所有区间运算都在段端点上进行（加法、乘积、挖空、指示化、差分），成本
   与段数而非时间宽度成正比。

## 命令行

```bash
python3 -I intervalrules/cli.py setup    # 运行时自检
python3 -I intervalrules/cli.py verify   # 内置断言 + 参考模型 fuzz
python3 -I intervalrules/cli.py demo     # 供应链合规更正演示
python3 -I intervalrules/cli.py run \
    --program examples/program.json \
    --changes examples/changes.json --read R
```

`-I` 使用隔离模式；从仓库根目录运行即可导入 `intervalrules` 包。

## 测试

```bash
python3 -I intervalrules/cli.py verify   # 含独立逐整数参考模型的随机对拍
python3 -I tests/test_engine.py          # 规格级独立测试
```
