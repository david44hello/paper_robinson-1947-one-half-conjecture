// Robinson 1947, Program A, HOLQ support fork, 20261102__09:35 EST.
// Version 0.40 — Program A,20261102__10:40 EST: regroup repeated Q; direct analytic principal-Log derivatives; same value/branch/cap/root.
// Compile without fast-math: g++ -std=c++17 -O2 -fno-fast-math ...
#include <array>
#include <algorithm>
#include <cmath>
#include <complex>
#include <csignal>
#include <ctime>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
#include <boost/multiprecision/cpp_int.hpp>
using namespace std;
struct Rational {
    uint64_t numerator=0,denominator=1;
    string text()const{return to_string(numerator)+"/"+to_string(denominator);}
};
static Rational lambda_coefficient,mu_coefficient;
static string support_kind;
static Rational parse_rational(const string& value){
    size_t slash=value.find('/');
    if(slash==string::npos||slash==0||slash+1==value.size()||value.find('/',slash+1)!=string::npos)
        throw runtime_error("coefficient must be exact NUM/DEN");
    string numerator=value.substr(0,slash),denominator=value.substr(slash+1);
    auto digits=[](const string& text){return all_of(text.begin(),text.end(),[](char item){return item>='0'&&item<='9';});};
    if(!digits(numerator)||!digits(denominator))throw runtime_error("nonnegative rational required");
    uint64_t top=stoull(numerator),bottom=stoull(denominator);
    if(bottom==0||top>(1ULL<<30)||bottom>(1ULL<<30))throw runtime_error("rational components out of exact range");
    uint64_t divisor=gcd(top,bottom);return Rational{top/divisor,bottom/divisor};
}
static void configure_support(const string& lambda,const string& mu,const string& kind){
    lambda_coefficient=parse_rational(lambda);mu_coefficient=parse_rational(mu);support_kind=kind;
    bool even=support_kind=="EVEN_VALUE"&&mu_coefficient.numerator==0;
    bool joint=support_kind=="JOINT_P55"&&lambda_coefficient.text()=="4/5"&&mu_coefficient.text()=="1/2";
    if(!even&&!joint)throw runtime_error("support kind/weights mismatch: EVEN_VALUE(mu=0) or JOINT_P55(4/5,1/2)");
}
static volatile sig_atomic_t stop_requested=0;
static void request_stop(int){stop_requested=1;}

static double down(double value){return nextafter(value,-numeric_limits<double>::infinity());}
static double up(double value){return nextafter(value,numeric_limits<double>::infinity());}
struct I {
    double lo,hi;
    I(double value=0):lo(value),hi(value){}
    I(double low,double high):lo(low),hi(high){if(!(low<=high))throw logic_error("invalid interval");}
};
static I operator+(I first,I second){return I(down(first.lo+second.lo),up(first.hi+second.hi));}
static I operator-(I value){return I(-value.hi,-value.lo);}
static I operator-(I first,I second){return first+(-second);}
static I operator*(I first,I second){
    array<double,4> products={first.lo*second.lo,first.lo*second.hi,first.hi*second.lo,first.hi*second.hi};
    return I(down(*min_element(products.begin(),products.end())),up(*max_element(products.begin(),products.end())));
}
static I operator/(I first,I second){
    if(second.lo<=0&&second.hi>=0)throw runtime_error("interval division through zero");
    return first*I(down(1/second.hi),up(1/second.lo));
}
static I rational_bound(const Rational& value){return I(double(value.numerator))/I(double(value.denominator));}
static double magnitude(I value){return max(abs(value.lo),abs(value.hi));}
static I square(I value){
    double low=value.lo<=0&&value.hi>=0?0:min(value.lo*value.lo,value.hi*value.hi);
    return I(max(0.,down(low)),up(max(value.lo*value.lo,value.hi*value.hi)));
}
static I root(I value){
    if(value.lo<=0)throw runtime_error("nonpositive square-root interval");
    double low=down(sqrt(value.lo)), high=up(sqrt(value.hi));
    while(up(low*low)>value.lo)low=down(low);
    while(down(high*high)<value.hi)high=up(high);
    return I(low,high);
}
static I pi_bound(){return I(3141592653589793.)/I(1e15)+I(0,1.1e-15);}

// Taylor remainders are explicit. No libm transcendental value is used as a bound.
static I sine_point(double value){
    if(abs(value)>8)throw runtime_error("sine argument beyond certified range");
    I xx(value), term(value), total(value);
    for(int index=1;index<=32;index++){
        term=term*(-xx*xx)/I((2*index)*(2*index+1)); total=total+term;
    }
    return total+I(-1e-30,1e-30); // 8^67/67! < 1e-30.
}
static I cosine_point(double value){
    if(abs(value)>8)throw runtime_error("cosine argument beyond certified range");
    I xx(value),term(1),total(1);
    for(int index=1;index<=32;index++){
        term=term*(-xx*xx)/I((2*index-1)*(2*index));total=total+term;
    }
    return total+I(-1e-30,1e-30); // 8^66/66! < 1e-30.
}
static I trig_range(I value,bool sine){
    double middle=value.lo/2+value.hi/2;
    double radius=up(max(middle-value.lo,value.hi-middle));
    I point=sine?sine_point(middle):cosine_point(middle);
    return I(max(-1.,down(point.lo-radius)),min(1.,up(point.hi+radius)));
}
static I exponential_point(double value){
    if(abs(value)>8)throw runtime_error("exp argument beyond certified range");
    I reduced=I(value)/I(4),term(1),total(1);
    for(int index=1;index<=32;index++){term=term*reduced/I(index);total=total+term;}
    total=total+I(-1e-24,1e-24); // e^2*2^33/33! < 1e-24.
    total=total*total;return total*total;
}
static I exponential(I value){return I(exponential_point(value.lo).lo,exponential_point(value.hi).hi);}
static I atanh_point(double value){
    if(abs(value)>.6)throw runtime_error("atanh argument beyond certified range");
    I xx(value),term(value),total(0);
    for(int index=0;index<64;index++){total=total+term/I(2*index+1);term=term*xx*xx;}
    return total+I(-1e-28,1e-28); // .6^129/[129*(1-.36)] < 1e-28.
}
static I inverse_hyperbolic(I value){return I(atanh_point(value.lo).lo,atanh_point(value.hi).hi);}
static I atan_small_point(double value){
    if(abs(value)>.4)throw runtime_error("atan argument beyond certified range");
    I xx(value),term(value),total(0);
    for(int index=0;index<40;index++){total=total+term/I(2*index+1);term=term*(-xx*xx);}
    return total+I(-1e-32,1e-32); // .4^81/81 < 1e-32.
}
// General real logarithm: frexp is exact binary range reduction; no libm log bound.
static I logarithm_point(double value){
    if(!(value>0)||!isfinite(value))throw runtime_error("nonpositive or nonfinite log argument");
    int exponent=0;double mantissa=frexp(value,&exponent)*2;exponent--;
    I ratio=(I(mantissa)-I(1))/(I(mantissa)+I(1));
    I log_two=I(2)*inverse_hyperbolic(I(1)/I(3));
    return I(exponent)*log_two+I(2)*inverse_hyperbolic(ratio);
}
static I logarithm(I value){return I(logarithm_point(value.lo).lo,logarithm_point(value.hi).hi);}
static I atanh_general(I value){
    if(!(value.lo>-1&&value.hi<1))throw runtime_error("atanh domain unresolved");
    return (logarithm(I(1)+value)-logarithm(I(1)-value))/I(2);
}
static I atan_point(double value){
    if(!isfinite(value))throw runtime_error("nonfinite atan argument");
    if(value<0)return -atan_point(-value);
    if(value>2){
        I reciprocal=I(1)/I(value);
        return pi_bound()/I(2)-I(atan_point(reciprocal.lo).lo,atan_point(reciprocal.hi).hi);
    }
    if(value<.5){
        I reduced=I(value)/(I(1)+root(I(1)+square(I(value))));
        return I(2)*I(atan_small_point(reduced.lo).lo,atan_small_point(reduced.hi).hi);
    }
    I argument=(I(value)-I(1))/(I(value)+I(1));
    return pi_bound()/I(4)+I(atan_small_point(argument.lo).lo,atan_small_point(argument.hi).hi);
}
static I inverse_tangent(I value){return I(atan_point(value.lo).lo,atan_point(value.hi).hi);}

struct D {
    I val; array<I,4> grad; array<array<I,4>,4> hess;
    D(I value=I(0)):val(value){
        for(I& item:grad)item=I(0);
        for(auto& row:hess)for(I& item:row)item=I(0);
    }
    static D variable(I value,int index){D out(value);out.grad[index]=I(1);return out;}
};
static D operator+(D first,D second){
    D out(first.val+second.val);
    for(int j=0;j<4;j++){out.grad[j]=first.grad[j]+second.grad[j];for(int k=0;k<4;k++)out.hess[j][k]=first.hess[j][k]+second.hess[j][k];}
    return out;
}
static D operator-(D value){
    D out(-value.val);
    for(int j=0;j<4;j++){out.grad[j]=-value.grad[j];for(int k=0;k<4;k++)out.hess[j][k]=-value.hess[j][k];}
    return out;
}
static D operator-(D first,D second){return first+(-second);}
static D operator*(D first,D second){
    D out(first.val*second.val);
    for(int j=0;j<4;j++){
        out.grad[j]=first.grad[j]*second.val+first.val*second.grad[j];
        for(int k=0;k<4;k++)out.hess[j][k]=first.hess[j][k]*second.val+first.grad[j]*second.grad[k]+first.grad[k]*second.grad[j]+first.val*second.hess[j][k];
    }
    return out;
}
static D operator/(D first,D second){
    D out(first.val/second.val);
    for(int j=0;j<4;j++)out.grad[j]=(first.grad[j]-out.val*second.grad[j])/second.val;
    for(int j=0;j<4;j++)for(int k=0;k<4;k++)
        out.hess[j][k]=(first.hess[j][k]-out.val*second.hess[j][k]-out.grad[j]*second.grad[k]-out.grad[k]*second.grad[j])/second.val;
    return out;
}
static D unary(D value,I answer,I derivative,I second){
    D out(answer);
    for(int j=0;j<4;j++){
        out.grad[j]=derivative*value.grad[j];
        for(int k=0;k<4;k++)out.hess[j][k]=derivative*value.hess[j][k]+second*value.grad[j]*value.grad[k];
    }
    return out;
}
static D sine(D value){return unary(value,trig_range(value.val,true),trig_range(value.val,false),-trig_range(value.val,true));}
static D cosine(D value){return unary(value,trig_range(value.val,false),-trig_range(value.val,true),-trig_range(value.val,false));}
static D expd(D value){I answer=exponential(value.val);return unary(value,answer,answer,answer);}
static D sqrtd(D value){I answer=root(value.val);return unary(value,answer,I(1)/(I(2)*answer),-I(1)/(I(4)*answer*answer*answer));}
static D atanhd(D value){I den=I(1)-square(value.val);return unary(value,atanh_general(value.val),I(1)/den,I(2)*value.val/(den*den));}
static D atand(D value){I den=I(1)+square(value.val);return unary(value,inverse_tangent(value.val),I(1)/den,-I(2)*value.val/(den*den));}

static D squared(D value){return unary(value,square(value.val),I(2)*value.val,I(2));}
static D logd(D value){return unary(value,logarithm(value.val),I(1)/value.val,-I(1)/square(value.val));}

struct C {D real,imag;C(D rr=D(),D ii=D()):real(rr),imag(ii){}};
static C operator+(C first,C second){return C(first.real+second.real,first.imag+second.imag);}
static C operator-(C first,C second){return C(first.real-second.real,first.imag-second.imag);}
static C operator*(C first,C second){return C(first.real*second.real-first.imag*second.imag,first.real*second.imag+first.imag*second.real);}
static C operator*(D first,C second){return C(first*second.real,first*second.imag);}
static C conjugate(C value){return C(value.real,-value.imag);}
static C expc(C value){D scale=expd(value.real);return C(scale*cosine(value.imag),scale*sine(value.imag));}
static C sinec(C value){
    D positive=expd(value.imag),negative=expd(-value.imag);
    D ch=(positive+negative)/D(I(2)),sh=(positive-negative)/D(I(2));
    return C(sine(value.real)*ch,cosine(value.real)*sh);
}
static C cosinec(C value){
    D positive=expd(value.imag),negative=expd(-value.imag);
    D ch=(positive+negative)/D(I(2)),sh=(positive-negative)/D(I(2));
    return C(cosine(value.real)*ch,-sine(value.real)*sh);
}
static I intersect(I first,I second){return I(max(first.lo,second.lo),min(first.hi,second.hi));}
static D intersect(D first,D second){
    D out(intersect(first.val,second.val));
    for(int j=0;j<4;j++){
        out.grad[j]=intersect(first.grad[j],second.grad[j]);
        for(int k=0;k<4;k++)out.hess[j][k]=intersect(first.hess[j][k],second.hess[j][k]);
    }
    return out;
}
static C phase(D value){return C(cosine(value),sine(value));}
struct CInterval {I real,imag;};
static CInterval complex_product(CInterval first,CInterval second){
    return {first.real*second.real-first.imag*second.imag,
            first.real*second.imag+first.imag*second.real};
}
static CInterval complex_difference(CInterval first,CInterval second){
    return {first.real-second.real,first.imag-second.imag};
}
static C principal_log(C value,int halfplane){
    if(!((halfplane==1&&value.imag.val.lo>0)||(halfplane==-1&&value.imag.val.hi<0)))
        throw runtime_error("principal Log half-plane unresolved");
    I norm=square(value.real.val)+square(value.imag.val);
    D real(logarithm(norm)/I(2));
    D imag(I(halfplane)*pi_bound()/I(2)-inverse_tangent(value.real.val/value.imag.val));
    C result(real,imag);
    CInterval reciprocal={value.real.val/norm,-value.imag.val/norm};
    CInterval reciprocal_square=complex_product(reciprocal,reciprocal);
    for(int first=0;first<4;first++){
        CInterval first_derivative={value.real.grad[first],value.imag.grad[first]};
        CInterval gradient=complex_product(reciprocal,first_derivative);
        result.real.grad[first]=gradient.real;result.imag.grad[first]=gradient.imag;
        for(int second=0;second<4;second++){
            CInterval second_derivative={value.real.grad[second],value.imag.grad[second]};
            CInterval mixed_derivative={value.real.hess[first][second],value.imag.hess[first][second]};
            CInterval hessian=complex_difference(complex_product(reciprocal,mixed_derivative),
                complex_product(reciprocal_square,complex_product(first_derivative,second_derivative)));
            result.real.hess[first][second]=hessian.real;result.imag.hess[first][second]=hessian.imag;
        }
    }
    return result;
}
static D even_ce(D theta){
    D aa(-logarithm(I(3)/I(4))/I(2));
    D real_ze=-logd(D(I(17)/I(16))-D(I(.5))*cosine(theta))/D(I(4));
    D ce=D(I(2))*sqrtd(aa*aa-squared(real_ze));
    return ce;
}
static I integer_bound(const string& text){
    bool negative=!text.empty()&&text[0]=='-';I result(0);
    for(size_t index=negative?1:0;index<text.size();index++){
        char item=text[index];if(item<'0'||item>'9')throw logic_error("bad embedded integer");
        result=result*I(10)+I(item-'0');
    }
    return negative?-result:result;
}
static I large_rational_bound(const string& text){
    size_t slash=text.find('/');
    if(slash==string::npos)throw logic_error("bad embedded rational");
    return integer_bound(text.substr(0,slash))/integer_bound(text.substr(slash+1));
}
static C dividec(C first,C second){
    D den=squared(second.real)+squared(second.imag);
    return C((first.real*second.real+first.imag*second.imag)/den,
             (first.imag*second.real-first.real*second.imag)/den);
}
using Exact=boost::multiprecision::cpp_rational;
using BigInteger=boost::multiprecision::cpp_int;
using ExactMatrix=array<array<Exact,4>,4>;
static const string joint_packet_sha="29c2322a33a23bdf6b0380f6f9ab1882bbc706005779d9d106172e8fc76f1afe";
static Exact exact_rational(const string& text){
    size_t slash=text.find('/');
    return Exact(BigInteger(text.substr(0,slash)))/Exact(BigInteger(text.substr(slash+1)));
}
static ExactMatrix exact_product(const ExactMatrix& first,const ExactMatrix& second){
    ExactMatrix result{};
    for(int row=0;row<4;row++)for(int col=0;col<4;col++)for(int inner=0;inner<4;inner++)
        result[row][col]+=first[row][inner]*second[inner][col];
    return result;
}
static ExactMatrix exact_positive_inverse(ExactMatrix matrix){
    ExactMatrix result{};for(int index=0;index<4;index++)result[index][index]=1;
    array<Exact,4> expected={exact_rational("8473/5000"),exact_rational("499588663/100000000"),
        exact_rational("1317395036843/1000000000000"),exact_rational("125044355055249/2000000000000000")};
    Exact minor=1;
    for(int col=0;col<4;col++){
        Exact pivot=matrix[col][col];minor*=pivot;
        if(!(pivot>0)||minor!=expected[col])throw logic_error("canonical P positivity/minor mismatch");
        for(int item=0;item<4;item++){matrix[col][item]/=pivot;result[col][item]/=pivot;}
        for(int row=0;row<4;row++)if(row!=col){
            Exact factor=matrix[row][col];
            for(int item=0;item<4;item++){
                matrix[row][item]-=factor*matrix[col][item];result[row][item]-=factor*result[col][item];
            }
        }
    }
    return result;
}
static array<Exact,9> exact_joint_coefficients(){
    array<array<int,4>,4> integers={{{16946,3451,-992,2537},{3451,30184,856,-108},
        {-992,856,2733,-344},{2537,-108,-344,879}}};
    ExactMatrix positive{},coupling{};
    for(int row=0;row<4;row++)for(int col=0;col<4;col++)positive[row][col]=Exact(integers[row][col])/10000;
    coupling[0][1]=coupling[1][0]=-Exact(8)/5;
    coupling[0][2]=coupling[2][0]=coupling[1][3]=coupling[3][1]=-Exact(1)/2;
    ExactMatrix correction=exact_product(exact_product(coupling,exact_positive_inverse(positive)),coupling),kk{};
    for(int row=0;row<4;row++)for(int col=0;col<4;col++)kk[row][col]=(positive[row][col]+correction[row][col])/2;
    return {(kk[0][0]+kk[1][1])/2,(kk[0][0]-kk[1][1])/2,kk[0][1],
        (kk[2][2]+kk[3][3])/2,(kk[2][2]-kk[3][3])/2,kk[2][3],
        kk[0][2]+kk[1][3],kk[0][2]-kk[1][3],kk[0][3]+kk[1][2]};
}
static const array<I,9>& joint_coefficients(){
    static array<I,9> coefficients=[](){
        array<Exact,9> exact=exact_joint_coefficients();array<I,9> bounded;
        for(int index=0;index<9;index++){
            string text=numerator(exact[index]).str()+"/"+denominator(exact[index]).str();
            bounded[index]=large_rational_bound(text);
        }
        return bounded;
    }();
    return coefficients;
}
static D joint_cap(D theta){
    const array<I,9>& coefficients=joint_coefficients();
    C zz(D(I(.25))*cosine(theta),D(I(.25))*sine(theta));
    C denominator=C(D(I(1)))-zz;
    if(!(denominator.real.val.lo>0))throw runtime_error("even kernel right half-plane unresolved");
    D real_ze=-logd(squared(denominator.real)+squared(denominator.imag))/D(I(4));
    D imag_ze=-atand(denominator.imag/denominator.real)/D(I(2));
    C ll=dividec(zz,denominator),mm=dividec(D(I(2))*zz,denominator*denominator);
    array<D,9> basis={D(-logarithm(I(3)/I(4))/I(2)),real_ze,imag_ze,
        D(I(8)/I(9)),mm.real,mm.imag,D(I(1)/I(3)),ll.real,ll.imag};
    D cap;
    for(int index=0;index<9;index++)cap=cap+D(coefficients[index])*basis[index];
    return cap;
}
struct Components {C quotient,even_difference,jet_value,objective;D ce,cap;};
static Components evaluate_forms(D theta,C aaform,C bbform,C ccform){
    C fourc=D(I(4))*ccform;
    C ell=D(I(2))*(aaform-bbform)+C(-fourc.imag,fourc.real);
    C ellw=D(I(2))*(aaform-bbform)-C(-fourc.imag,fourc.real);
    C kk=D(I(2))*(aaform+bbform);
    C pval=expc(ell),qval=expc(ellw);
    D tau=sine(theta/D(I(4)))/cosine(theta/D(I(4)));
    C chi=tau*(C(D(),D(I(1)))*expc(kk));
    C vminus=(D(I(1))/tau)*(C(D(),D(I(-1)))*expc(C(-kk.real,-kk.imag)));
    C original=C(D(I(1)))+D(I(.5))*(pval+qval)+D(I(.25))*((pval-qval)*(chi+vminus));
    C realform=C(D(I(1)))+expc(D(I(2))*(aaform-bbform))*cosinec(fourc)
        +D(I(.5))*(((D(I(1))/tau)*expc(D(I(-4))*bbform)-tau*expc(D(I(4))*aaform))*sinec(fourc));
    C quotient=C(intersect(original.real,realform.real),intersect(original.imag,realform.imag));
    C delta=C(D(),theta/D(I(2)))-principal_log(C(D(I(1)))+chi,1)
        +principal_log(C(D(I(1)))-chi,-1);
    C even_difference=delta+C(-fourc.imag,fourc.real);
    C imaginary_u=C(-even_difference.imag,even_difference.real);
    C jet_value=pval+qval-quotient;
    D ce=even_ce(theta);
    D cap=support_kind=="EVEN_VALUE"?D(rational_bound(lambda_coefficient))*ce:joint_cap(theta);
    D mu(rational_bound(mu_coefficient));
    C objective=(D(I(1))-mu)*quotient+mu*(pval+qval)
        +D(rational_bound(lambda_coefficient))*imaginary_u-C(cap);
    return Components{quotient,even_difference,jet_value,objective,ce,cap};
}
static C quotient(array<D,4> variables){
    D alpha=variables[0],psi=variables[1],omega=variables[2],theta=variables[3];
    D half=theta/D(I(2));
    D aa(inverse_hyperbolic(I(.5)));
    D zzreal=D(I(.5))*atanhd(D(I(4)/I(5))*cosine(half));
    D zzimag=D(I(.5))*atand(D(I(4)/I(3))*sine(half));
    D first=sqrtd((aa+zzreal)/D(I(2)));
    D cross=zzimag/(D(I(2))*first);
    D last=sqrtd((aa-zzreal)/D(I(2))-cross*cross);
    C pp=phase(psi),ww=phase(omega);
    array<C,3> matrix={cosine(alpha)*(pp*ww),sine(alpha)*(pp*C(D(),D(I(1)))),cosine(alpha)*(pp*conjugate(ww))};
    C aaform=(first*first)*matrix[0];
    C bbform=(cross*cross)*matrix[0]+(D(I(2))*cross*last)*matrix[1]+(last*last)*matrix[2];
    C ccform=(first*cross)*matrix[0]+(first*last)*matrix[1];
    return evaluate_forms(theta,aaform,bbform,ccform).objective;
}

struct Box {array<I,4> axes;int depth=0;uint64_t id=1;};
static array<D,4> variables(const Box& box,bool center){
    array<D,4> out;
    for(int j=0;j<4;j++){
        I axis=box.axes[j];double middle=axis.lo/2+axis.hi/2;
        out[j]=D::variable(center?I(middle):axis,j);
    }
    return out;
}
static void tests(){
    // Exact Taylor remainder checks are additionally documented for independent replay.
    for(double value:{-3.,-1.,0.,1.,3.}){
        I ee=exponential(I(value)),ss=trig_range(I(value),true),cc=trig_range(I(value),false);
        if(!(ee.lo<=exp(value)&&ee.hi>=exp(value)&&ss.lo<=sin(value)&&ss.hi>=sin(value)&&cc.lo<=cos(value)&&cc.hi>=cos(value)))throw runtime_error("elementary sanity test");
    }
    double piv=acos(-1.);
    for(double degrees:{90.,110.,135.})for(int sign:{1,-1}){
        Box box;box.axes={I(0),I(sign==1?0:piv),I(0),I(degrees*piv/180)};
        C result=quotient(variables(box,true));
        complex<double> zz=.5*exp(complex<double>(0,degrees*piv/360)),ww=conj(zz);
        auto ff=[sign](complex<double> value){return value/pow(1.-double(sign)*value,2);};
        auto fp=[sign](complex<double> value){return (1.+double(sign)*value)/pow(1.-double(sign)*value,3);};
        complex<double> expected=1.+(zz*fp(zz)-ww*fp(ww))/(ff(zz)-ff(ww));
        complex<double> expected_u=.5*(log(1.-zz*zz)-log(1.-ww*ww));
        double even_aa=-.5*log(.75),even_real=-.5*log(1.-zz*zz).real();
        double ce=2*sqrt(even_aa*even_aa-even_real*even_real);
        double lambda=double(lambda_coefficient.numerator)/lambda_coefficient.denominator;
        double mu=double(mu_coefficient.numerator)/mu_coefficient.denominator;
        double cap=lambda*ce;
        if(support_kind=="JOINT_P55"){
            I enclosure=joint_cap(D(I(degrees*piv/180))).val;
            cap=enclosure.lo/2+enclosure.hi/2;
        }
        complex<double> sump=zz*fp(zz)/ff(zz)+ww*fp(ww)/ff(ww);
        expected=(1-mu)*expected+lambda*complex<double>(0,1)*expected_u+mu*sump-cap;
        if(!(result.real.val.lo<=expected.real()+1e-12&&result.real.val.hi>=expected.real()-1e-12))throw runtime_error("Koebe normalization");
    }
    cout<<"TEST PASS: elementary enclosures and supported Koebe rotations at90/110/135deg\n";
}
static void cover(I lowdeg,I highdeg,uint64_t maxnodes,double target,const string& filename,double cpu_seconds){
    if(!(cpu_seconds>0))throw runtime_error("CPU budget must be positive");
    const clock_t started=clock();
    signal(SIGTERM,request_stop);signal(SIGINT,request_stop);
    I piv=pi_bound();Box initial;
    // Conjugation half-chart reduction: checked independently by two other reviewers.
    if(!(lowdeg.lo>0&&highdeg.hi<=180&&lowdeg.hi<highdeg.lo))throw runtime_error("invalid degree root");
    initial.axes={I(0,up(piv.hi/2)),I(-up(piv.hi/2),up(piv.hi/2)),I(-piv.hi,piv.hi),I((lowdeg*piv/I(180)).lo,(highdeg*piv/I(180)).hi)};
    vector<Box> pending={initial};uint64_t count=0,leaves=0,nextid=2;double minbound=1e100;
    ofstream output(filename);output<<hexfloat;
    output<<"ROOT";for(I axis:initial.axes)output<<' '<<axis.lo<<' '<<axis.hi;output<<'\n';
    output<<"SUPPORT "<<lambda_coefficient.text()<<' '<<mu_coefficient.text()<<' '<<support_kind<<'\n';
    while(!pending.empty()&&count<maxnodes&&!stop_requested&&double(clock()-started)/CLOCKS_PER_SEC<cpu_seconds){
        Box box=pending.back();pending.pop_back();count++;
        int dimension=3;double lower=-1e100;bool evaluated=false;char reason='?';
        try{
            C value=quotient(variables(box,false));C center=quotient(variables(box,true));
            double deduction=0,linear=0,quadratic=0,largest=-1;
            for(int j=0;j<4;j++){
                double mid=box.axes[j].lo/2+box.axes[j].hi/2;
                double rad=up(max(mid-box.axes[j].lo,box.axes[j].hi-mid));
                double item=up(magnitude(value.real.grad[j])*rad);deduction=up(deduction+item);
                linear=up(linear+up(magnitude(center.real.grad[j])*rad));
                for(int k=0;k<4;k++){
                    double kmid=box.axes[k].lo/2+box.axes[k].hi/2;
                    double krad=up(max(kmid-box.axes[k].lo,box.axes[k].hi-kmid));
                    quadratic=up(quadratic+up(up(magnitude(value.real.hess[j][k])*rad)*krad));
                }
                if(item>largest){largest=item;dimension=j;}
            }
            double natural=value.real.val.lo,mean=down(center.real.val.lo-deduction),taylor=down(down(center.real.val.lo-linear)-up(.5*quadratic));
            lower=max({natural,mean,taylor});reason=lower==natural?'N':(lower==mean?'M':'T');evaluated=true;
        }catch(const runtime_error&){
            // Principal-log domain failures may require a phase split, not theta alone.
            double widest=-1;
            for(int axis=0;axis<4;axis++){
                double width=(box.axes[axis].hi-box.axes[axis].lo)/(initial.axes[axis].hi-initial.axes[axis].lo);
                if(width>widest){widest=width;dimension=axis;}
            }
        }
        if(evaluated&&lower>target){
            leaves++;minbound=min(minbound,lower);output<<"L "<<box.id<<' '<<lower<<' '<<reason<<'\n';continue;
        }
        if(box.depth>=80)throw runtime_error("max depth reached without proof");
        double mid=box.axes[dimension].lo/2+box.axes[dimension].hi/2;
        Box left=box,right=box;left.axes[dimension].hi=mid;right.axes[dimension].lo=mid;
        left.depth=right.depth=box.depth+1;left.id=nextid++;right.id=nextid++;
        output<<"S "<<box.id<<' '<<dimension<<' '<<mid<<' '<<left.id<<' '<<right.id<<'\n';
        pending.push_back(right);pending.push_back(left);
        if(count%10000==0)cerr<<"nodes="<<count<<" accepted="<<leaves<<" pending="<<pending.size()<<" depth="<<box.depth<<'\n';
    }
    for(const Box& box:pending){output<<"P "<<box.id<<' '<<box.depth;for(I axis:box.axes)output<<' '<<axis.lo<<' '<<axis.hi;output<<'\n';}
    output<<"END "<<(pending.empty()?"PASS":"INCOMPLETE")<<' '<<count<<' '<<leaves<<' '<<minbound<<'\n';
    output<<"CPU "<<double(clock()-started)/CLOCKS_PER_SEC<<" STOP_REQUESTED "<<stop_requested<<'\n';
    cout<<setprecision(17)<<"status="<<(pending.empty()?"PASS":"INCOMPLETE")<<" nodes="<<count<<" leaves="<<leaves<<" pending="<<pending.size()<<" min_bound="<<minbound<<'\n';
}
int main(int argc,char** argv){
    try{
        if(argc<5||string(argv[1])!="--support")throw runtime_error("required prefix: --support LAMBDA MU CSUP-KIND");
        configure_support(argv[2],argv[3],argv[4]);argc-=4;argv+=4;
        if(support_kind=="JOINT_P55")joint_coefficients();
        if(argc==2&&string(argv[1])=="--describe-support"){
            cout<<"SUPPORT "<<lambda_coefficient.text()<<' '<<mu_coefficient.text()<<' '<<support_kind<<'\n';
            if(support_kind=="JOINT_P55"){
                cout<<"PACKET_SHA256 "<<joint_packet_sha<<'\n';
                for(const Exact& value:exact_joint_coefficients())cout<<numerator(value)<<'/'<<denominator(value)<<'\n';
            }
            return 0;
        }
        if(argc==16&&string(argv[1])=="--forms-box"){
            array<I,7> values;
            for(int index=0;index<7;index++)values[index]=I(stod(argv[2+2*index]),stod(argv[3+2*index]));
            Components parts=evaluate_forms(D(values[0]),C(D(values[1]),D(values[2])),
                C(D(values[3]),D(values[4])),C(D(values[5]),D(values[6])));
            cout<<setprecision(17);
            for(C value:{parts.quotient,parts.even_difference,parts.jet_value,parts.objective})
                cout<<value.real.val.lo<<' '<<value.real.val.hi<<' '<<value.imag.val.lo<<' '<<value.imag.val.hi<<' ';
            cout<<parts.ce.val.lo<<' '<<parts.ce.val.hi<<' '<<parts.cap.val.lo<<' '<<parts.cap.val.hi<<'\n';return 0;
        }
        if(argc==2&&string(argv[1])=="--test"){tests();return 0;}
        if(argc==6&&string(argv[1])=="--evaluate"){
            Box box;cout<<setprecision(17);
            for(int j=0;j<4;j++){double point=stod(argv[j+2]);box.axes[j]=I(point);cout<<point<<' ';}
            C value=quotient(variables(box,true));
            cout<<value.real.val.lo<<' '<<value.real.val.hi;
            for(I item:value.real.grad)cout<<' '<<item.lo<<' '<<item.hi;
            for(auto row:value.real.hess)for(I item:row)cout<<' '<<item.lo<<' '<<item.hi;
            cout<<'\n';return 0;
        }
        if(argc==7&&string(argv[1])=="--probe"){
            Box box;double halfwidth=stod(argv[6]);if(!(halfwidth>0))throw runtime_error("probe needs positive radius");
            for(int j=0;j<4;j++){double point=stod(argv[j+2]);box.axes[j]=I(down(point-halfwidth),up(point+halfwidth));}
            C value=quotient(variables(box,false)),center=quotient(variables(box,true));
            double mean=0,linear=0,quadratic=0;
            for(int j=0;j<4;j++){
                double mid=box.axes[j].lo/2+box.axes[j].hi/2;
                double rad=up(max(mid-box.axes[j].lo,box.axes[j].hi-mid));
                mean=up(mean+up(magnitude(value.real.grad[j])*rad));
                linear=up(linear+up(magnitude(center.real.grad[j])*rad));
                for(int k=0;k<4;k++){
                    double kmid=box.axes[k].lo/2+box.axes[k].hi/2;
                    double krad=up(max(kmid-box.axes[k].lo,box.axes[k].hi-kmid));
                    quadratic=up(quadratic+up(up(magnitude(value.real.hess[j][k])*rad)*krad));
                }
            }
            cout<<setprecision(17)<<center.real.val.lo<<' '<<value.real.val.lo<<' '
                <<down(center.real.val.lo-mean)<<' '
                <<down(down(center.real.val.lo-linear)-up(.5*quadratic))<<'\n';return 0;
        }
        if(argc==8&&string(argv[1])=="--pilot"){
            cover(rational_bound(parse_rational(argv[2])),rational_bound(parse_rational(argv[3])),stoull(argv[4]),stod(argv[6]),argv[7],stod(argv[5]));return 0;
        }
        if(argc!=7||string(argv[1])!="--cover")throw runtime_error("usage: --test OR --cover LOW HIGH NODES TARGET OUTPUT OR --pilot LOW HIGH NODES CPU_SECONDS TARGET OUTPUT");
        cover(rational_bound(parse_rational(argv[2])),rational_bound(parse_rational(argv[3])),stoull(argv[4]),stod(argv[5]),argv[6],numeric_limits<double>::infinity());
        return 0;
    }catch(const exception& error){cerr<<"FAIL: "<<error.what()<<'\n';return 2;}
}
