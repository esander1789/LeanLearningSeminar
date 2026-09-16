#include <type_traits>
#include <cstdint>

static_assert(std::is_same<signed short, int16_t>::value);

struct Zero {};

template<typename T>
struct Succ {};

using One = Succ<Zero>;
using Two = Succ<One>;
using Three = Succ<Two>;
using Four = Succ<Three>;


// equality
static_assert(std::is_same<Two, Two>::value);
// static_assert(std::is_same<Two, One>::value);


// addition
// addition needs two types and returns a result type
struct dummy_t {};
template<typename N, typename M>
struct Add {
    using result_t = dummy_t; // this is really a dummy type
};

// two specializations of the template we are going to use
// add n zero = n
// add n (succ m) = succ (add n m)

template<typename N>
struct Add<N, Zero> {
  using result_t = N;
};

template<typename N, typename M>
struct Add<N, Succ<M>> {
  using result_t = Succ<typename Add<N, M>::result_t>;
};

static_assert(std::is_same<Four, Add<Two, Two>::result_t>::value);
int main(){}
