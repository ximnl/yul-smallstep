# yul-smallstep

LMap.thy -- 基于列表的映射

Syntax.thy -- Yul语言语法的形式化

Typing.thy --  Yul语言类型系统的形式化

SmallStep.thy -- Yul语言小步可执行语义的形式化

tests -- 类型系统和小步语义的测试
  tests/Common_defs.thy -- 测试用例、辅助函数的定义
  tests/Tests_Typing.thy -- 类型系统的测试
  tests/Tests_Language.thy -- Yul语言特性的测试
  tests/TestsBuiltin_Arithmetic.thy -- 算术运算内建函数的测试
  tests/TestsBuiltin_Logic.thy -- 逻辑运算内建函数的测试
  tests/TestsBuiltin_MemSto.thy -- 内存、存储操作内建函数的测试
  tests/TestsBuiltin_ExeCtrl.thy -- 控制流内建函数（如外部调用）的测试
  tests/TestsBuiltin_SttQue.thy -- 区块链状态读取内建函数的测试

case-study -- ERC20代币合约MyToken的类型检查和基于小步语义的执行
  case-study/CallFuncs.thy -- MyToken合约各个接口函数的执行
  case-study/RunToken.thy -- 合约在调用transfer_func函数的输入下的执行
