import cocotb
from .. import helper

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()
    await hs_dut.assert_pure_io([0, 5], [None])
    # await hs_dut.assert_pure_io([0, 50], [0])
