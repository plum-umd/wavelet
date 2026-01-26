import cocotb
from .. import helper

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()
    await hs_dut.assert_pure_io([0, 5, 0], [sum(range(6))])
    await hs_dut.assert_pure_io([0, 50, 0], [sum(range(51))])
