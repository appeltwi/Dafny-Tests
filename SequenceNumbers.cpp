#include <iostream>
#include <cstdint>
#include <limits>
#include <cstdlib>
		

using IntegerT = uint8_t;

constexpr auto lim16 = std::numeric_limits<IntegerT>::max() /2;

bool compare_seq_less(IntegerT bi1, IntegerT bi2)
{
    return (bi1 < bi2 && (bi2 - bi1) < lim16) || (bi1 > bi2 && (bi1 - bi2) > lim16);
}

struct SeqNum
{
    IntegerT _seq_number;
    friend constexpr std::partial_ordering operator<=>(SeqNum lhs, SeqNum rhs)
    {
        if (lhs._seq_number == rhs._seq_number)
        {
            return std::partial_ordering::equivalent;
        }
        else if (compare_seq_less(lhs._seq_number, rhs._seq_number))
        {
            return std::partial_ordering::less;
        }
        else if (compare_seq_less(rhs._seq_number, lhs._seq_number))
        {
            return std::partial_ordering::greater;           
        }
        else
        {
            return std::partial_ordering::unordered; 
        }

    }
    friend std::ostream& operator<<(std::ostream& os, SeqNum s)
    {
        return os << '(' << static_cast<int>(s._seq_number) << ')';
    }
};

void print_three_way_comparison(const auto& p, const auto& q)
{
    const auto cmp{p <=> q};
    std::cout << p
              << (cmp < 0 ? " <  " : cmp > 0 ? " >  " : cmp == 0 ? " == " : " unordered ") // compares with 0
              << q << '\n';
}

int main()
{
    const SeqNum p1{0}, p2{1}, p3{lim16}, p4{1}, p5{lim16*2};
    for (IntegerT j = 0; j <= lim16*2; ++j)
    {    
        for (IntegerT i = 0; i <= lim16*2; ++i)
        {
        SeqNum  p{i};
        SeqNum  p0{j};        
        print_three_way_comparison(p0, p);
        }
    }            
    return 0;
}
