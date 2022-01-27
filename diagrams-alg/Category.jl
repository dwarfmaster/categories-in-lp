
module Categories

export id, is_identity, composition, src, dst

function id() end
function is_identity() end
function composition() end
function src() end
function dst() end

id(x :: String) = String[]
is_identity(v :: Vector{String}) = isempty(v)
composition(f :: Vector{String}, g :: Vector{String}) = vcat(g, f)
src(names :: Vector{String}) = isempty(names) ? "s" : string("s_", names[begin])
dst(names :: Vector{String}) = isempty(names) ? "s" : string("d_", names[end])

function test()
    println(id("tata"))
    println(is_identity(id("toto")))
    println(src(["hello", "world"]))
    println(dst(["hello", "world"]))
    println(composition(["hello"], ["world"]))
end
end

