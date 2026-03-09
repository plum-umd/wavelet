
T-Load:
Ψ′= ([𝑝′],Ψpend ++ [𝑝_out],Ψgarb) Ψ′ ⊢ 𝐸𝑓 ~~> 𝐸𝑔
-------------------------------------------------
Ψ ⊢ let 𝑦= load(𝐴,𝑖); 𝐸𝑓 ~~>
    let 𝑝_sync, 𝑝′ = jnsplt(Ψsync);
    let 𝑦, 𝑝_out = load(𝐴, 𝑖, 𝑝_sync); 𝐸𝑔

T-Store:
Ψ′= ([𝑝′],Ψpend ++ [𝑝_out],Ψgarb) Ψ′ ⊢ 𝐸𝑓 ~~> 𝐸𝑔
-------------------------------------------------
Ψ ⊢ let () = store(𝐴,𝑖,𝑣); 𝐸𝑓 ~~>
    let 𝑝_sync, 𝑝′ = jnsplt(Ψsync); 
    let (), 𝑝_out = store(𝐴, 𝑖, 𝑣, 𝑝_sync); 𝐸𝑔

T-Call:
Ψ′ = ([𝑝′],Ψpend ++ [𝑝_ret],[p_garb]) Ψ′ ⊢ 𝐸𝑓 ~~> 𝐸𝑔
--------------------------------------------------
Ψ ⊢ let 𝑦-> = 𝑓(𝑥->); 𝐸𝑓 ~~>
    let 𝑝_sync, 𝑝′ = jnsplt(Ψsync);
    let p_𝜖, p_garb = jnsplt(Ψgarb);
    let 𝑦->, 𝑝_ret = 𝑓(𝑥->, 𝑝_sync, p_ε); 𝐸𝑔

T-Return:
--------------------------------------------------------
Ψ ⊢ 𝑥 ~~> let 𝑝_ret, 𝑝_𝜖 = jnsplt(Ψsync++Ψpend++Ψgarb);
          ret(𝑥, 𝑝_ret)

T-TailCall:
------------------------------------------------------------
Ψ ⊢ f(𝑥->) ~~> let 𝑝_sync, 𝑝′ = jnsplt(Ψsync);
               let p_garb, p_𝜖 = jnsplt(Ψpend++[p']++Ψgarb);
               f(𝑥->, 𝑝_sync, p_garb)

T-If:
Ψ ⊢ 𝐸𝑓 ~~> 𝐸𝑔   Ψ ⊢ 𝐸′𝑓 ~~> 𝐸′𝑔
------------------------------------------------
Ψ ⊢ if 𝑥 then 𝐸𝑓 else 𝐸′𝑓 ~~> 
    if 𝑥 then 𝐸𝑔 else 𝐸′𝑔

T-Fence:
Ψ′ = fence(Ψ)    Ψ′ ⊢ 𝐸𝑓 ~~> 𝐸𝑔
----------------------------------
Ψ ⊢ — 𝐸𝑓 ~~> 𝐸𝑔

fence(Ψ) = (Ψsync ++ Ψpend, [])
