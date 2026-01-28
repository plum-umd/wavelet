import cocotb
from .. import helper

@cocotb.test()
async def test(dut):
    hs_dut = helper.HandshakeDut(dut)
    await hs_dut.init()
    await hs_dut.assert_io(
        [5], [None],
        init_memory={
            "weight": [1, 2, 3, 4, 5],
            "src": [5, 4, 3, 2, 1],
        },
        expected_memory={
            "dest": [6, 6, 6, 6, 6],
        },
    )
    await hs_dut.assert_io(
        [0], [None],
        init_memory={
            "weight": [],
            "src": [],
        },
        expected_memory={
            "dest": [],
        },
    )
