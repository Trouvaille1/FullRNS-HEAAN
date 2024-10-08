/*
* Copyright (c) by CryptoLab inc.
* This program is licensed under a
* Creative Commons Attribution-NonCommercial 3.0 Unported License.
* You should have received a copy of the license along with this
* work.  If not, see <http://creativecommons.org/licenses/by-nc/3.0/>.
*/

#ifndef HEAANNTT_CONTEXT_H_
#define HEAANNTT_CONTEXT_H_

#include <complex>
#include <chrono>
#include <map>

#include "Common.h"
#include "Numb.h"

#define Q0_BIT_SIZE 61 //见原论文A Full RNS Variant of Approximate Homomorphic Encryption，第5.1节。选择Logq_0约等于61

using namespace std;

static string LOGARITHM = "Logarithm"; ///< log(x)
static string EXPONENT  = "Exponent"; ///< exp(x)
static string SIGMOID   = "Sigmoid"; ///< sigmoid(x) = exp(x) / (1 + exp(x))

class Context {
public:
	//所有函数实现中，处理[0,L)使用q系列的成员变量和成员函数，处理[L,k)使用p系列的成员变量和成员函数

	// Encryption parameters
	long logN; ///< Logarithm of Ring Dimension
	long logNh; ///< Logarithm of Ring Dimension - 1
	long L; ///< Maximum Level that we want to support
	long K; ///< The number of special modulus (usually L + 1) 在testEncodeBatch中K==L，在testBasic中为K==L+1

	long N;//环系统中多项式模次数
	long M;//指的是M阶分圆多项式（环的多项式模）。这里M=2*N，M是2的幂，所以M阶分圆多项式的次数为M/2=N
	long Nh;//N/2

	long logp;
	long p;//可能是放大系数delta

	long h;///< parameter for HWT distribution 默认值为64
	double sigma;///< standard deviation for Gaussian distribution 默认值为3.2

	uint64_t* qVec;//Primes. 长度为L的uint64_t数组。为L个RNS基. 注意，第i个模数qVec[i]的倒数1/qVec[i]=qrVec[i]>>qTwok[i]
	uint64_t* pVec;//Special Primes.长度为K

	uint64_t* qrVec; // Barrett reduction 长度为L。预计算的Barrett reduction中计算模数倒数需要用到的值
	uint64_t* prVec; // Barrett recution 长度为K

	long* qTwok; // Barrett reduction 长度为L.是Barrett reduction中计算模数倒数需要用到的幂次。
	long* pTwok; // Barrett reduction 长度为K

	uint64_t* qkVec; // Montgomery reduction 长度为L
	uint64_t* pkVec; // Montgomery reduction 长度为K

	uint64_t* qdVec; //长度为L. 值为两倍的qVec 用在qiINTTAndEqual()中
	uint64_t* pdVec; //长度为K

	uint64_t* qInvVec; //长度为L 在qiNTTAndEqual()中调用。为qVec的倒数
	uint64_t* pInvVec; //长度为K

	uint64_t* qRoots; //长度为L。qRoots[i]为NTT中等价的2n次单位根psi=g_(2n)。这里用2n次单位根的原因是要用负循环卷积来规避在R_q中的多项式乘法中NTT需要补零的问题
	uint64_t* pRoots;

	uint64_t* qRootsInv; //长度为L
	uint64_t* pRootsInv;

	uint64_t** qRootPows; //形状为L*N的二维矩阵。//qRootPows[i][jprime]=qRoots[i]^j mod mod=g^j mod mod.所以，qRootPows[i][j]=qRoots[i]^jprime mod mod
	uint64_t** pRootPows;

	uint64_t** qRootPowsInv; //长度为L
	uint64_t** pRootPowsInv;

	uint64_t* NInvModq; //长度为L
	uint64_t* NInvModp;

	uint64_t** qRootScalePows; //形状为L*N的二维矩阵，用于NTT。qRootScalePows是qRootPows放大两次2^32后的结果
	uint64_t** pRootScalePows;

	uint64_t** qRootScalePowsOverq; //长度为L
	uint64_t** pRootScalePowsOverp;

	uint64_t** qRootScalePowsInv; //长度为L
	uint64_t** pRootScalePowsInv;

	uint64_t* NScaleInvModq; // [i] //长度为L
	uint64_t* NScaleInvModp; // [k]

	uint64_t** qHatModq; // [l][i] (phat_i)_l mod p_i
	uint64_t* pHatModp; // [k] qhat_k mod q_k

	uint64_t** qHatInvModq; // [l][i] (qhat_i)_l^-1 mod q_i
	uint64_t* pHatInvModp; // [k] phat_k^-1 mod p_k

	uint64_t*** qHatModp; // [l] [i] [k]  (phat_i)_l mod q_k

	uint64_t** pHatModq; // [k][i] qhat_k mod p_i

	uint64_t* PModq; // [i] qprod mod p_i
	uint64_t* PInvModq; // [i] qprod mod p_i

	uint64_t** QModp; // [i] qprod mod p_i
	uint64_t** QInvModp; // [i] qprod mod p_i

	uint64_t** qInvModq; // [i][j] p_i^-1 mod p_j

	long* rotGroup; ///< precomputed rotation group indexes 用于确定旋转因子次数的辅助数组。rotGroup[i]=5^i mod M < auxiliary information about rotation group indexes for batch encoding

	complex<double>* ksiPows; ///< precomputed ksi powers FFT旋转因子，ksiPows[k]=e^(2k*pai*i/M)< storing ksi pows for fft calculation

	map<string, double*> taylorCoeffsMap; ///< precomputed taylor coefficients

	uint64_t* p2coeff;
	uint64_t* pccoeff;
	uint64_t* p2hcoeff;

	Context(long logN, long logp, long L, long K, long h = 64, double sigma = 3.2);

	void arrayBitReverse(complex<double>* vals, const long size);
	void arrayBitReverse(uint64_t* vals, const long size);

	void fft(complex<double>* vals, const long size);
	void fftInvLazy(complex<double>* vals, const long size);
	void fftInv(complex<double>* vals, const long size);

	void fftSpecial(complex<double>* vals, const long size);
	void fftSpecialInvLazy(complex<double>* vals, const long size);
	void fftSpecialInv(complex<double>* vals, const long size);

	//真正执行encode操作的函数
	void encode(uint64_t* ax, complex<double>* vals, long slots, long l);
	void encode(uint64_t* ax, double* vals, long slots, long l);

	void encodeSingle(uint64_t* ax, complex<double>& val, long l);
	void encodeSingle(uint64_t* ax, double val, long l);

	void decode(uint64_t* ax, complex<double>* vals, long slots, long l);
	void decode(uint64_t* ax, double* vals, long slots, long l);

	void decodeSingle(uint64_t* ax, complex<double>& val, long l);
	void decodeSingle(uint64_t* ax, double val, long l);

	void qiNTT(uint64_t* res, uint64_t* a, long index);
	void piNTT(uint64_t* res, uint64_t* a, long index);

	//没有直接使用这个函数，而是使用NTTAndEqual(...)
	void NTT(uint64_t* res, uint64_t* a, long l, long k = 0);

	void qiNTTAndEqual(uint64_t* a, long index);
	void piNTTAndEqual(uint64_t* a, long index);

	//NTT常用函数.k默认值为0
	void NTTAndEqual(uint64_t* a, long l, long k = 0);

	void qiINTT(uint64_t* res, uint64_t* a, long index);
	void piINTT(uint64_t* res, uint64_t* a, long index);

	void INTT(uint64_t* res, uint64_t* a, long l, long k = 0);

	void qiINTTAndEqual(uint64_t* a, long index);
	void piINTTAndEqual(uint64_t* a, long index);

	void INTTAndEqual(uint64_t* a, long l, long k = 0);

	void qiNegate(uint64_t* res, uint64_t* a, long index);
	void piNegate(uint64_t* res, uint64_t* a, long index);

	void negate(uint64_t* res, uint64_t* a, long l, long k = 0);

	void qiNegateAndEqual(uint64_t* a, long index);
	void piNegateAndEqual(uint64_t* a, long index);

	void negateAndEqual(uint64_t* a, long l, long k = 0);

	void qiAddConst(uint64_t* res, uint64_t* a, uint64_t c, long index);
	void piAddConst(uint64_t* res, uint64_t* a, uint64_t c, long index);

	void addConst(uint64_t* res, uint64_t* a, uint64_t c, long l, long k = 0);

	void qiAddConstAndEqual(uint64_t* a, uint64_t c, long index);
	void piAddConstAndEqual(uint64_t* a, uint64_t c, long index);

	void addConstAndEqual(uint64_t* a, uint64_t c, long l, long k = 0);

	void qiSubConst(uint64_t* res, uint64_t* a, uint64_t c, long index);
	void piSubConst(uint64_t* res, uint64_t* a, uint64_t c, long index);

	void subConst(uint64_t* res, uint64_t* a, uint64_t c, long l, long k = 0);

	void qiSubConstAndEqual(uint64_t* a, uint64_t c, long index);
	void piSubConstAndEqual(uint64_t* a, uint64_t c, long index);

	void subConstAndEqual(uint64_t* a, uint64_t c, long l, long k = 0);

	void qiAdd(uint64_t* res, uint64_t* a, uint64_t* b, long index);
	void piAdd(uint64_t* res, uint64_t* a, uint64_t* b, long index);

	void add(uint64_t* res, uint64_t* a, uint64_t* b, long l, long k = 0);

	void qiAddAndEqual(uint64_t* a, uint64_t* b, long index);
	void piAddAndEqual(uint64_t* a, uint64_t* b, long index);

	void addAndEqual(uint64_t* a, uint64_t* b, long l, long k = 0);

	void qiSub(uint64_t* res, uint64_t* a, uint64_t* b, long index);
	void piSub(uint64_t* res, uint64_t* a, uint64_t* b, long index);

	void sub(uint64_t* res, uint64_t* a, uint64_t* b, long l, long k = 0);

	void qiSubAndEqual(uint64_t* a, uint64_t* b, long index);
	void piSubAndEqual(uint64_t* a, uint64_t* b, long index);

	void subAndEqual(uint64_t* a, uint64_t* b, long l, long k = 0);

	void qiSub2AndEqual(uint64_t* a, uint64_t* b, long index);
	void piSub2AndEqual(uint64_t* a, uint64_t* b, long index);

	void sub2AndEqual(uint64_t* a, uint64_t* b, long l, long k = 0);

	void qiMulConst(uint64_t* res, uint64_t* a, uint64_t cnst, long index);
	void piMulConst(uint64_t* res, uint64_t* a, uint64_t cnst, long index);

	void mulConst(uint64_t* res, uint64_t* a, uint64_t cnst, long l, long k = 0);

	void qiMulConstAndEqual(uint64_t* res, uint64_t cnst, long index);
	void piMulConstAndEqual(uint64_t* res, uint64_t cnst, long index);

	void mulConstAndEqual(uint64_t* res, uint64_t cnst, long l, long k = 0);

	void qiMul(uint64_t* res, uint64_t* a, uint64_t* b, long index);
	void piMul(uint64_t* res, uint64_t* a, uint64_t* b, long index);

	void mul(uint64_t* res, uint64_t* a, uint64_t* b, long l, long k = 0);

	void mulKey(uint64_t* res, uint64_t* a, uint64_t* b, long l);

	void qiMulAndEqual(uint64_t* a, uint64_t* b, long index);
	void piMulAndEqual(uint64_t* a, uint64_t* b, long index);

	void mulAndEqual(uint64_t* a, uint64_t* b, long l, long k = 0);

	void qiSquare(uint64_t* res, uint64_t* a, long index);
	void piSquare(uint64_t* res, uint64_t* a, long index);

	void square(uint64_t* res, uint64_t* a, long l, long k = 0);

	void qiSquareAndEqual(uint64_t* a, long index);
	void piSquareAndEqual(uint64_t* a, long index);

	void squareAndEqual(uint64_t* a, long l, long k = 0);

	void evalAndEqual(uint64_t* a, long l);

	void raiseAndEqual(uint64_t*& a, long l);
	void raise(uint64_t* res, uint64_t* a, long l);

	void backAndEqual(uint64_t*& a, long l);
	void back(uint64_t* res, uint64_t* a, long l);

	void reScaleAndEqual(uint64_t*& a, long l);
	void reScale(uint64_t* res, uint64_t* a, long l);

	void modDownAndEqual(uint64_t*& a, long l, long dl);
	uint64_t* modDown(uint64_t* a, long l, long dl);

	void leftRot(uint64_t* res, uint64_t* a, long l, long rotSlots);
	void leftRotAndEqual(uint64_t* a, long l, long rotSlots);

	void conjugate(uint64_t* res, uint64_t* a, long l);
	void conjugateAndEqual(uint64_t* a, long l);

	void mulByMonomial(uint64_t* res, uint64_t* a, long l, long mdeg);
	void mulByMonomialAndEqual(uint64_t* a, long l, long mdeg);

	////从Z^N中抽取一个N维多项式向量，其中每一个系数都是取自方差为sigma^2的离散高斯分布
	void sampleGauss(uint64_t* res, long l, long k = 0);

	//对于[0,1]的实数rou，从{0,1,-1}中抽取一个N维向量，其中抽取到1和-1的概率为rou/2，抽取到0的概率为1-rou
	void sampleZO(uint64_t* res, long s, long l, long k = 0);

	void sampleUniform(uint64_t* res, long l, long k = 0);

	//从{0,1,-1}中抽取一个N维向量，该向量的汉明重量（非0元素个数）=h
	void sampleHWT(uint64_t* res, long l, long k = 0);
	
};

#endif
