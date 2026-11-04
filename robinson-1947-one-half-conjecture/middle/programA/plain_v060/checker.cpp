// Robinson 1947, Program A, 20261101__20:09 ET.
// Version 0.60 — Program A,20261101__22:51 ET: leaf-reason records for bounded half-chart pilot; interval arithmetic unchanged from v0.30.
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
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
static volatile sig_atomic_t stop_requested=0;
static void request_stop(int){stop_requested=1;}

static double down(double value){return nextafter(value,-numeric_limits<double>::infinity());}
static double up(double value){return nextafter(value,numeric_limits<double>::infinity());}
struct I {
    double lo,hi;
    I(double value=0):lo(value),hi(value){}
    I(double low,double high):lo(low),hi(high){if(!(low<=high))throw runtime_error("invalid interval");}
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
static I atan_point(double value){
    if(value<.5||value>1.5)throw runtime_error("atan transform range");
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
static D atanhd(D value){I den=I(1)-square(value.val);return unary(value,inverse_hyperbolic(value.val),I(1)/den,I(2)*value.val/(den*den));}
static D atand(D value){I den=I(1)+square(value.val);return unary(value,inverse_tangent(value.val),I(1)/den,-I(2)*value.val/(den*den));}

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
static C bilinear(array<C,2> first,array<C,3> matrix,array<C,2> second){
    return first[0]*matrix[0]*second[0]+first[1]*matrix[2]*second[1]
         +first[0]*matrix[1]*second[1]+first[1]*matrix[1]*second[0];
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
    array<C,2> avec={C(first,cross),C(D(),last)};
    array<C,2> bvec={conjugate(avec[0]),conjugate(avec[1])};
    C pp=phase(psi),ww=phase(omega);
    array<C,3> matrix={cosine(alpha)*(pp*ww),sine(alpha)*(pp*C(D(),D(I(1)))),cosine(alpha)*(pp*conjugate(ww))};
    C ell=D(I(2))*bilinear(avec,matrix,avec),ellw=D(I(2))*bilinear(bvec,matrix,bvec);
    C kk=D(I(2))*bilinear(avec,matrix,bvec);
    C pval=expc(ell),qval=expc(ellw);
    D tau=sine(theta/D(I(4)))/cosine(theta/D(I(4)));
    C vplus=tau*(C(D(),D(I(1)))*expc(kk));
    C vminus=(D(I(1))/tau)*(C(D(),D(I(-1)))*expc(C(-kk.real,-kk.imag)));
    C original=C(D(I(1)))+D(I(.5))*(pval+qval)+D(I(.25))*((pval-qval)*(vplus+vminus));
    C aaform=(first*first)*matrix[0];
    C bbform=(cross*cross)*matrix[0]+(D(I(2))*cross*last)*matrix[1]+(last*last)*matrix[2];
    C ccform=(first*cross)*matrix[0]+(first*last)*matrix[1];
    C fourc=D(I(4))*ccform;
    C realform=C(D(I(1)))+expc(D(I(2))*(aaform-bbform))*cosinec(fourc)
        +D(I(.5))*(((D(I(1))/tau)*expc(D(I(-4))*bbform)-tau*expc(D(I(4))*aaform))*sinec(fourc));
    return C(intersect(original.real,realform.real),intersect(original.imag,realform.imag));
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
        if(!(result.real.val.lo<=expected.real()+1e-12&&result.real.val.hi>=expected.real()-1e-12))throw runtime_error("Koebe normalization");
    }
    cout<<"TEST PASS: elementary enclosures and both Koebe rotations at90/110/135deg\n";
}
static void cover(double lowdeg,double highdeg,uint64_t maxnodes,double target,const string& filename,double cpu_seconds){
    if(!(cpu_seconds>0))throw runtime_error("CPU budget must be positive");
    const clock_t started=clock();
    signal(SIGTERM,request_stop);signal(SIGINT,request_stop);
    I piv=pi_bound();Box initial;
    // Conjugation half-chart reduction: checked independently by two other reviewers.
    initial.axes={I(0,up(piv.hi/2)),I(-up(piv.hi/2),up(piv.hi/2)),I(-piv.hi,piv.hi),I(down(lowdeg*piv.lo/180),up(highdeg*piv.hi/180))};
    vector<Box> pending={initial};uint64_t count=0,leaves=0,nextid=2;double minbound=1e100;
    ofstream output(filename);output<<hexfloat;
    output<<"ROOT";for(I axis:initial.axes)output<<' '<<axis.lo<<' '<<axis.hi;output<<'\n';
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
        }catch(const runtime_error&){dimension=3;}
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
            cover(stod(argv[2]),stod(argv[3]),stoull(argv[4]),stod(argv[6]),argv[7],stod(argv[5]));return 0;
        }
        if(argc!=7||string(argv[1])!="--cover")throw runtime_error("usage: --test OR --cover LOW HIGH NODES TARGET OUTPUT OR --pilot LOW HIGH NODES CPU_SECONDS TARGET OUTPUT");
        cover(stod(argv[2]),stod(argv[3]),stoull(argv[4]),stod(argv[5]),argv[6],numeric_limits<double>::infinity());
        return 0;
    }catch(const exception& error){cerr<<"FAIL: "<<error.what()<<'\n';return 2;}
}

