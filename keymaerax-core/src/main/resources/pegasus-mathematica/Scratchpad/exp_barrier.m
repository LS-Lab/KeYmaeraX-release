% SOS vector barrier certificates

clear; echo on;
pvar x1 x2;
vars = [x1; x2];

%Working example (using 2D vector barrier + deg 2 polynomials):
field = [ x2; (-x1 + x1^3/3 -x2)];
init_true = 0.25 - ((x1-1.5)^2 + x2^2);
unsafe_true = 0.16 - ((x1+1)^2 +(x2+1)^2) ;

%field = [x1^4 + 2*x1*x2^2 - 6*x1^2*x2^2 + x2^4 + x1*(x1^2 - x2^2);
%         2*x1^2*x2 - 4*x1^3*x2 + 4*x1*x2^3 - x2*(x1^2 - x2^2)]
%init_true = 1/4 - ((-1 + x1)^2 + (1 + x2)^2);
%unsafe_true = x2-1 ;

barrier_dim = 1;
maxdeg = 2;
maxsosdeg = 4;
monvec = monomials([x1;x2],0:1:maxdeg);
monvec2 = monomials([x1;x2],0:1:maxsosdeg);

eps = 0.001;

%The initial choice of diagL is very problem specific...
diagL = [-1];

% The initial fixed SOSes for everything other than the first barrier coordinate
%fFP(1) = 0;
for i = 1: barrier_dim
    fFP(i) = 1;
end

%Tolerance in error minimization
tol = 1e-4;
%Tolerance in feasibility
feas_tol = 0.95;
%polynomial coefficient tolerance
poly_tol = 1e-6;
%maximum final error
err_tol = 1e-5;
best_err = 1.0;
%set things to 0
reduce_poly = true;

while true
    %The 'barrier' iteration
    l_err = 0.0;
    h_err = best_err;
    err = 0.5 * (h_err + l_err);
    A = ones(barrier_dim,barrier_dim) - eye(barrier_dim) + diag(diagL);
    initialrun = true;
    
    while true
        fprintf('BARRIER ITERATION %f\n',err);

        %This 'error function' is very problem specific ...
        init = init_true - sum(vars.^2)*err;
        unsafe = unsafe_true - sum(vars.^2)*err;

        prog = sosprogram(vars);
        % The m-D vector barrier certificate (B1,...,Bm)
        %B = zeros(1,barrier_dim);
        for i=1:barrier_dim
            [prog,B(i)] = sospolyvar(prog,monvec);
        end

        % SOSes for each barrier in init
        for i=1:barrier_dim
            [prog,IP(i)] = sossosvar(prog,monvec2);
        end

        % SOS for final coordinate
        [prog,FP] = sossosvar(prog,monvec2,'wscoeff');

        % Constrain initial states on all components : - SOS*init - Bi >= 0
        for i=1:barrier_dim
            prog = sosineq(prog, -IP(i) * init - B(i));
        end

        % Constrain final state
        fpB = sum(fFP.*B);
        prog = sosineq(prog, (fpB - FP*unsafe)- eps);

        %Lie derivatives for each component
        for i=1:barrier_dim
            dB(i) = 0*vars(1);
            for j = 1:length(vars)
                dB(i) = dB(i)+diff(B(i),vars(j))*field(j);
            end
        end

        expr = A * transpose(B) - transpose(dB);

        for i = 1:barrier_dim
            prog = sosineq(prog,expr(i));
        end

        opt.params.fid = 0;
        prog = sossolve(prog,opt);

        feasibility = prog.solinfo.info.feasratio;
        if feasibility > feas_tol
            h_err = err;
            best_sol = prog;
            best_err = h_err;
            initialrun = false;
        else
            if initialrun
                fprintf('resetting error\n');
                h_err = 2.0 * h_err;
            else
                l_err = err;
            end
        end
        
        err = 0.5 * (h_err + l_err);
        if err - l_err < tol
            break
        end
    end

    best_err
    B2 = [[[[sosgetsol(best_sol,B)]]]]
    
    if reduce_poly
        all_truncated = true;
        %for i = 1:barrier_dim
           % [t,B2(i)] = truncate_coeffs(B2(i),poly_tol);
           % all_truncated = all_truncated && t;
        %end
        if all_truncated
            fprintf('fully truncated\n')
            break
        end
    end
    
    B = B2
    if best_err < err_tol
        fprintf('min err achieved %f\n',best_err)
        break
    end

    %The 'SOS' iteration fixes the barriers but allows free choice of SOSes
    l_err = 0.0;
    h_err = best_err;
    err = 0.5 * (h_err + l_err);
    clear fFP;
    clear diagL;
    initialrun = true;

    while true
        fprintf('SOS ITERATION %f\n',err);
        %This 'error function' is very problem specific ...
        init = init_true - sum(vars.^2)*err;
        unsafe = unsafe_true - sum(vars.^2)*err;

        prog = sosprogram(vars);

        % SOSes for each barrier in init
        for i=1:barrier_dim
            [prog,IP(i)] = sossosvar(prog,monvec2);
        end

        % Constrain initial states on all components : - SOS*init - Bi >= 0
        for i=1:barrier_dim
            prog = sosineq(prog, -IP(i) * init - B(i));
        end

        % SOS for final coordinate
        [prog,FP] = sossosvar(prog,monvec2,'wscoeff');

        % SOSes for everything other than the first barrier coordinate
        %fFP(1) = 0*vars(1);
        for i = 1: barrier_dim
            [prog,fFP(i)] = sossosvar(prog,monvec2);
        end

        % Constrain final state
        fpB = sum(fFP.*B);
        prog = sosineq(prog, (fpB - FP*unsafe - eps));

        %Lie derivatives for each component
        for i=1:barrier_dim
            dB(i) = 0*vars(1);
            for j = 1:length(vars)
                dB(i) = dB(i)+diff(B(i),vars(j))*field(j);
            end
        end

        %Optimize for polynomials on the diagonal of A
        for i = 1:barrier_dim
            [prog,diagL(i)] = sospolyvar(prog,monvec);
        end

        A = ones(barrier_dim,barrier_dim) - eye(barrier_dim) + diag(diagL);

        expr = A * transpose(B) - transpose(dB);

        for i = 1:barrier_dim
            prog = sosineq(prog,expr(i));
        end

        opt.pars.fid = 0;
        prog = sossolve(prog,opt);
        feasibility = prog.solinfo.info.feasratio;
        if feasibility > feas_tol
            h_err = err;
            best_sol = prog;
            best_err = h_err;
            initialrun = false;
        else
            if initialrun
                fprintf('resetting error');
                h_err = 2.0 * h_err;
            else
                l_err = err;
            end
        end

        err = 0.5 * (h_err + l_err);
        if err - l_err < tol
            break
        end
    end

    best_err
    fFP = sosgetsol(best_sol,fFP)
    diagL = sosgetsol(best_sol,diagL)

    if reduce_poly
        for i = 1:barrier_dim
            [t,fFP(i)] = truncate_coeffs(fFP(i),poly_tol);
            [t,diagL(i)] = truncate_coeffs(diagL(i),poly_tol);
        end
    end
    
    fFP
    diagL
end