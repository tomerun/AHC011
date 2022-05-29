N = 10
rnd = Random.new(2)
edges = [] of Tuple(Int32, Int32)
N.times do |i|
  (N - 1).times do |j|
    edges << {i * N + j, i * N + j + 1}
  end
end
(N - 1).times do |i|
  N.times do |j|
    edges << {i * N + j, (i + 1) * N + j}
  end
end
edges.delete({(N - 1) * N + (N - 2), (N - 1) * N + (N - 1)})
edges.delete({(N - 2) * N + (N - 1), (N - 1) * N + (N - 1)})
set = Set(Array(Int32)).new
1.times do
  (edges.size - 1).times do |i|
    pos = rnd.rand(edges.size - i) + i
    edges[i], edges[pos] = edges[pos], edges[i]
  end
  uf = UnionFind.new(N * N - 1)
  tiles = Array.new(N) { Array.new(N, 0) }
  edges.each do |e|
    next if uf.find(e[0], e[1])
    uf.union(e[0], e[1])
    r0 = e[0] // N
    c0 = e[0] % N
    r1 = e[1] // N
    c1 = e[1] % N
    if r0 == r1
      tiles[r0][c0] |= 4
      tiles[r1][c1] |= 1
    else
      tiles[r0][c0] |= 8
      tiles[r1][c1] |= 2
    end
  end

  N.times do |i|
    N.times do |j|
      printf("%x", tiles[i][j])
    end
    puts
  end

  count = tiles.flatten.tally
  set << (1..15).map { |i| count.fetch(i, 0) }
end
puts set.size

class UnionFind
  def initialize(size : Int32)
    @root = Array(Int32).new(size, -1)
  end

  def union(i, j)
    a = root(i)
    b = root(j)
    if a != b
      @root[a] += @root[b]
      @root[b] = a
    end
  end

  def find(i, j)
    root(i) == root(j)
  end

  def root(i)
    return i if @root[i] < 0
    @root[i] = root(@root[i])
  end

  def size(i)
    -@root[root(i)]
  end
end
