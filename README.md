# Verification of Sparse Matrix Computations with Alloy

### CS 6110 Spring'21 Class Project
#### __Contributors__: Mahesh Lakshminarasimhan, Xinyi Li.


### Repo Structure
* __reference_impl__: The exisiting code from Dyer et al. available [here](https://people.engr.ncsu.edu/jwb/alloy/).
* __extensions__: Our extensions to the existing models that support the following:
    * `CSRtoELL`: Translation from the CSR to the ELL format.
        <br />&nbsp;&nbsp;&nbsp;&nbsp; Please check our [original repo](https://github.com/Mahesh-Lak/SpM-Alloy) to see the commits and hitory for this part. 
    * `COOtoCSR_mvmELL`: Translation from COO to CSR, and MVM with the ELL format.
* __paper_src__: Latex source files for the workshop paper write-up.
### Reproducing the bugs 
<br /> &nbsp;&nbsp;&nbsp;&nbsp;There are two bugs: 
* __bug1__: zero rows but >0 columns issue. <br>
      To reproduce it, 
       <p>     ``` cd reference_impl/translate.als```<p>
       run assertion `maxnzValid`. 
       <p> It will return a counterexample which has rows but multiple columns.<p>
* __bug2__: not strict `maxnz` issue. 
      To reproduce it,
    - find all code lines labeled as `enable the following line to reproduce bug 2`, and delete `/*` to enable the code. 
    - Then go to `translate.als` and run assertion `maxnzValid`. 
    
    This time, it will return a counterexample where all the lines in the ELL instance contain zero. As a result, we couldn't have a fixed `maxnz` for an ELL instance. 

<br /> P.S. If you are familiar with git, you could go to the [original repo](https://github.com/Mahesh-Lak/SpM-Alloy), and `git checkout` to the specific commit as the message demonstrate. 







