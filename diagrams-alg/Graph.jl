
include("Category.jl")

module Graphs

using ..Categories

const Step = @NamedTuple{to :: Int, mph :: Int}
mkStep(to, mph) = Step((to,mph))
const Path = Vector{Step}
const Face = NTuple{2,Path}

struct Graph{Obs,Mphs}
    nodes  :: Vector{Obs}
    arrows :: Array{Vector{Mphs},2}
    faces  :: Array{Vector{Face}, 2}
end

struct IncompatibleEndpoint <: Exception
    expected :: Int
    got :: Int
end

Base.size(gr :: Graph{O,M}) where {O,M} = size(gr.nodes)[1]

"Creates a graph with only one node"
node(:: Type{O}, :: Type{M}, x :: O) where {O,M} =
    Graph(O[x], fill(M[], (1,1)), fill(Face[], (1,1)))
"Juxtapose two graphs"
function juxtapose(g1 :: Graph{O,M}, g2 :: Graph{O,M}) where {O,M}
    nsize = size(g1) + size(g2)
    gr = Graph(vcat(g1.nodes, g2.nodes),
               [ M[] for i=1:nsize,j=1:nsize ],
               [ Face[] for i=1:nsize,j=1:nsize ])
    gr.arrows[begin:size(g1),begin:size(g1)] = g1.arrows
    gr.arrows[size(g1)+1:end,size(g1)+1:end] = g2.arrows
    gr.faces[begin:size(g1),begin:size(g1)] = g1.faces
    gr.faces[size(g1)+1:end,size(g1)+1:end] = g2.faces
    return gr
end
"Add a morphism between two nodes"
function connect!(gr :: Graph{O,M}, src, dst, m :: M) where {O,M}
    push!(gr.arrows[src,dst], m)
end
"Creates a graph with only one arrow"
function arrow(src :: O, dst :: O, m :: M) where {O,M}
    gr = juxtapose(node(O, M, src),node(O, M, dst))
    connect!(gr, 1, 2, m)
    return gr
end
"Add a face between two paths"
function fill!(gr :: Graph{O,M}, src, path1, path2) where {O,M}
    dst = path1[end].to
    dst != path2[end].to && throw(IncompatibleEndpoint(dst,path2[end].to))
    for (p1,p2) in gr.faces[src, dst]
        if p1 == path1 && p2 == path2
            return nothing
        elseif p1 == path2 && p2 == path1
            return nothing
        end
    end
    push!(gr.faces[src,dst], (path1,path2))
end


function test()
    g1 = node(String, String, "toto")
    g2 = node(String, String, "tata")
    println(g1)

    g3 = juxtapose(g1,g2)
    println(g3)
    println(arrow("s", "d", "hello-world"))

    connect!(g3, 1, 2, "arrow1")
    connect!(g3, 1, 2, "arrow2")
    fill!(g3, 1, [mkStep(2,1)], [mkStep(2,2)])
    fill!(g3, 1, [mkStep(2,1)], [mkStep(2,2)])
    fill!(g3, 1, [mkStep(2,2)], [mkStep(2,1)])
    println(g3)
end

end
