library(survival)
library(gss)
data(aids)
# all event times should be sorted

dtnpmle <- function(x, u, v, max_iter = 1000, error = 1e-9){
  dat <- cbind(x, u, v)[order(x), ]
  n <- nrow(dat)
  J <- apply(dat[, 2:3], MARGIN = 1, FUN = function(uvj) (uvj[1] <= dat[, 1]) & (dat[, 1] <= uvj[2]))
  inv_puv <- 1 / c(colMeans(J))
  inv_pt <- sum(inv_puv) / c(J %*% inv_puv)
  f <- inv_pt / sum(inv_pt)
  g <- inv_puv / sum(inv_puv)
  converged <- FALSE
  
  for (i in seq_len(max_iter)){
    inv_pt <- sum(inv_puv) / c(J %*% inv_puv)
    inv_puv <- sum(inv_pt) / c(t(inv_pt) %*% J)
    f_next <- inv_pt / sum(inv_pt)
    g_next <- inv_puv / sum(inv_puv)
    if (all(abs(c(f_next - f, g_next - g)) < error)){
      converged <- TRUE
      f <- f_next
      g <- g_next
      break
    }
    f <- f_next
    g <- g_next
  }
  
  masses <- data.frame(x = dat[, 1], u = dat[, 2], v = dat[, 3], f = f, g = g)
  jump_indx <- !duplicated(masses$x, fromLast = TRUE)
  return(list(cdf = cbind(x = masses$x[jump_indx], F = pmin(cumsum(masses$f)[jump_indx], 1)), 
              masses = masses, pt = c(1 / inv_pt), puv = c(1 / inv_puv), 
              converged = converged, n_iter = i))
}

stderr_weights <- function(x, u, v, npcdf){
  n <- length(x)
  C_lprod <- function(A) {rbind(A, -colSums(A))} # C %*% a
  C_rprod <- function(A) {sapply(seq_len(n - 1), FUN = function(i) A[, i] - A[, n])}
  Ct_lprod <- function(A) {sapply(seq_len(ncol(A)), FUN = function(i) A[-n, i] - A[n, i])}
  
  n_x <- sapply(npcdf[, 1, drop = TRUE], FUN = function(xi) sum(x == xi))
  npcdf <- rbind(c(min(u) - 1, 0), npcdf)
  Fv <- npcdf[findInterval(v, npcdf[, 1]), 2]
  Fu <- npcdf[findInterval(u, npcdf[, 1], left.open = TRUE), 2]
  Fvu <- Fv - Fu
  a <- c(n_x / (diff(npcdf[, 2]) * n))[match(x, npcdf[-1, 1])]
  Juv <- apply(cbind(u, v), MARGIN = 1, FUN = function(uvj) (uvj[1] <= x) & (x <= uvj[2])) # J[i,j]: u[j] <= x[i] <= v[j]
  
  S <- toeplitz(rep(1, n), r = c(1, rep(0, n-1)))
  S_inv <- toeplitz(c(1,-1, rep(0, n-2)), r = c(1, rep(0, n-1))) # solve(S)
  B <- S %*% diag(1 / (n * a))
  B_inv <- diag(n * a) %*% S_inv
  
  unique_indx <- !duplicated(x, fromLast = TRUE)
  match_unique_indx <- match(x, unique(x))
  H <- sapply(seq_len(n), 
              FUN = function(i) {((x[i] <= x[unique_indx]) / a[i]) - (cumsum(Juv[, i] / a^2)[unique_indx] / (n * Fvu[i]))})
  Atilde <- Juv %*% diag(1 / Fvu^2) %*% t(Juv) %*% S_inv / n
  A <- S %*% diag(1 / a^2) %*% Atilde / n
  IA <- -A
  diag(IA) <- 1 + diag(IA)
  L_F <- (B %*% C_lprod(solve(Ct_lprod(C_rprod(B_inv %*% IA %*% B)),
                              Ct_lprod(B_inv %*% H[match_unique_indx, ]))))[unique_indx, ]
  
  L_ainv <- sapply(seq_len(n), 
                   FUN = function(i) (-((Juv[, i] / Fvu[i]) - a - (Atilde %*% L_F[match_unique_indx, i])) / a^2))
  var_F <- rowMeans(L_F^2) / n
  var_ainv <- rowMeans(L_ainv^2) / n
  return(list(L_F = L_F, var_F = var_F, a = a, L_ainv = L_ainv, var_ainv = var_ainv))
}

sensitivity_analysis <- function(y, X, ipw, trunc_mass = seq(0, 1, by = 0.1),
                                 ipw_infl = NULL, time_wt = NULL, time_wt_infl = NULL, 
                                 max_iter = 100, error = 1e-7, beta_init = NULL,
                                 center_covariates = FALSE){
  
  coxph_rtrunc <- function(y, X, ipw, outer_wt, trunc_mass, ipw_avg, max_iter, error,
                           beta_init, n_ties, unique_indx, 
                           time_wt = NULL, ipw_infl = NULL, time_wt_infl = NULL){
    
    n_unique <- length(unique_indx)
    p <- ncol(X)
    tX <- t(X)
    beta_est <- beta_init
    converged <- FALSE
    for (i in seq_len(max_iter)){
      exps <- exp(c(X %*% beta_est))
      p_trunc <- trunc_mass^exps
      odds_trunc <- (p_trunc) / (1 - p_trunc)
      odds_wt <- ipw * exps * odds_trunc
      
      fit <- coxph(y ~ X, weights = ipw, init = beta_est, robust = FALSE, ties = "breslow",
                   control = coxph.control(iter.max = 0, timefix = FALSE))
      fit_detail <- coxph.detail(fit)
      if (p == 1){
        fit_detail$imat <- array(fit_detail$imat, dim = c(1, 1, n_unique))
        fit_detail$means <- cbind(fit_detail$means)
      }
      
      # not divided by n, evaluated at unique event times
      S0 <- ipw[unique_indx] * n_ties * exp(sum(fit$means * beta_est)) / fit_detail$hazard
      S1 <- diag(S0) %*% fit_detail$means
      S0_adj <- S0 + sum(odds_wt)
      riskset_avg <- sapply(seq_len(p), FUN = function(j) {(S1[, j] + sum(odds_wt * X[, j])) / S0_adj})
      est_fn <- ipw_avg - c(t(n_ties * outer_wt[unique_indx]) %*% riskset_avg)
      
      odds_wt2 <- ipw * exps^2 * odds_trunc * (1 + odds_trunc) * ifelse(trunc_mass > 0, log(trunc_mass), 0)
      S2_adjustment <- tX %*% diag(odds_wt + odds_wt2) %*% X
      derivative <- matrix(0, nrow = p, ncol = p) # negative derivative
      for (j in seq_len(n_unique)){
        indx <- unique_indx[j]
        derivative <- derivative + n_ties[j] * outer_wt[indx] * 
          (
            ((fit_detail$imat[, , j] / (n_ties[j] * ipw[indx])) + 
               c(fit_detail$means[j, ]) %*% fit_detail$means[j, , drop = FALSE]) * 
              S0[j] + S2_adjustment
          ) / S0_adj[j]
        derivative <- derivative - n_ties[j] * outer_wt[indx] * c(riskset_avg[j, ]) %*% riskset_avg[j, , drop = FALSE]
      }
      derivative <- derivative - c(t(outer_wt[unique_indx] * n_ties / S0_adj) %*% riskset_avg) %*% (t(odds_wt2) %*% X)
      
      beta_update <- solve(derivative, est_fn)
      
      
      # check convergence
      if (all(abs(beta_update) < error)){
        converged <- TRUE
        break
      }
      
      beta_est <- beta_est + beta_update
      
    }
    
    stderrs <- rep(NA, p)
    if (!is.null(ipw_infl)){
      haz <- n_ties * ipw[unique_indx] / S0_adj
      wtcumhaz <- c(0, cumsum(haz * time_wt[unique_indx]))
      integ_wtriskset_avg <- apply(riskset_avg, MARGIN = 2, FUN = function(x) c(0, cumsum(x * haz * time_wt[unique_indx])))
      riskset_avg <- rbind(0, riskset_avg)
      match_indx <- findInterval(y[, 1], y[unique_indx, 1]) + 1
      match_indx2 <- 1:n# match(y[, 1], unique(y[, 1]))
      
      # p by n
      sch_resids_uw <- (tX - t(riskset_avg[match_indx, ])) %*% diag(event_indx)
      score_resids_uw <- (sch_resids_uw %*% diag(time_wt)) - (tX %*% diag(exps * (wtcumhaz[match_indx] + odds_trunc * wtcumhaz[n_unique + 1])))
      score_resids_uw <- score_resids_uw + sapply(seq_len(n), FUN = function(i) {
        exps[i] * (integ_wtriskset_avg[match_indx[i], ] + odds_trunc[i] * integ_wtriskset_avg[n_unique + 1, ])
      })
      
      ipw_adj <- score_resids_uw %*% ipw_infl[match_indx2, ] / n
      var_components <- (score_resids_uw %*% diag(ipw)) + ipw_adj
      
      if (!is.null(time_wt_infl)){
        ipw_adj2 <- sch_resids_uw %*% diag(ipw) %*% time_wt_infl[match_indx2, ] / n
        var_components <- var_components + ipw_adj2
      }
      
      meat <- apply(var_components, MARGIN = 2, FUN = function(x) x %o% x)
      if (ncol(X) == 1){
        meat <- sum(meat)
      }else{
        meat <- rowSums(meat)
      }
      inv_derivative <- solve(derivative)
      var_est <- inv_derivative %*% matrix(meat, nrow = p) %*% t(inv_derivative)
      stderrs <- sqrt(diag(var_est))
      
    }
    
    if (!converged){
      stop("Error: algorithm did not converge")
    }
    return(list(coef = beta_est, se = stderrs))
  }
  
  n <- nrow(X)
  p <- ncol(X)
  if (ncol(y) != 2){
    stop("y should be a two-column Surv object")
  }
  if (2 %in% y[, 2]){
    event_indx <- y[, 2] == 2
  }else{
    event_indx <- as.logical(y[, 2])
  }
  
  if (is.null(beta_init)){
    beta_init <- rep(0, p)
  }
  
  if (is.null(time_wt)){
    outer_wt <- ipw
    time_wt <- rep(1, n)
  }else{
    time_wt <- time_wt + 1e-7
    outer_wt <- time_wt * ipw
    
  }
  
  if (center_covariates == TRUE){
    X <- scale(X, scale = FALSE)
  }
  
  ipw_avg <- c(t(outer_wt * event_indx) %*% X)
  unique_indx <- which(!duplicated(y[, 1], fromLast = TRUE) & event_indx)
  unique_times <- y[unique_indx, 1]
  n_ties <- sapply(unique_times, FUN = function(tj) sum(y[event_indx, 1] == tj))
  
  
  coef_ests <- matrix(NA, nrow = length(trunc_mass), ncol = p)
  stderrs <- matrix(NA, nrow = length(trunc_mass), ncol = p)
  for (j in seq_along(trunc_mass)){
    ests <- tryCatch(coxph_rtrunc(y = y, X = X, ipw = ipw, outer_wt = outer_wt,
                                  trunc_mass = trunc_mass[j], ipw_avg = ipw_avg, 
                                  max_iter = max_iter, error = error, 
                                  beta_init = beta_init,
                                  n_ties = n_ties, unique_indx = unique_indx, 
                                  time_wt = time_wt, ipw_infl = ipw_infl, time_wt_infl = time_wt_infl),
                     error = function(e) NULL)
    if (!is.null(ests) & !any(is.na(ests$coef))){
      coef_ests[j, ] <- ests$coef
      stderrs[j, ] <- ests$se
      beta_init <- ests$coef # improve convergence
    }
  }
  return(list(coef = coef_ests, trunc_mass = trunc_mass, se = stderrs))
}

dat <- aids
dat$baseline <- (1986*12 + 7) - dat$infe
dat$ltrunc <- (1982*12) - dat$baseline
dat$incu[dat$incu == 0] <- 0.5
dat <- dat[order(dat$incu), ]
dat$age_gp <- factor(ifelse(dat$age <= 4, "<=4", ifelse(dat$age <= 59, "4-59", ">59")), 
                     levels = c(">59", "4-59", "<=4"))
summary(dat)

npmle <- dtnpmle(dat$incu, dat$ltrunc, dat$infe)
igraph::is.connected(igraph::graph(unlist(sapply(seq_len(nrow(dat)), FUN = function(i) 
  c(rbind(i, which((dat$ltrunc <= dat$incu[i]) & (dat$incu[i] <= dat$infe))))))), "strong")
plot(npmle$masses$x/12, npmle$pt, xlab = "Years since infection", ylab = "Sampling Probability", ylim = c(0,1))

y <- Surv(dat$incu, rep(1, nrow(dat)))
X <- cbind(as.numeric(dat$age_gp == "<=4"), as.numeric(dat$age_gp == "4-59"))
match_indx <- findInterval(dat$incu, npmle$cdf[, 1])
infl <- stderr_weights(dat$incu, dat$ltrunc, dat$infe, npmle$cdf)
infl_a_est <- sapply(seq_len(nrow(dat)), FUN = function(i) {-infl$L_ainv[, i] * infl$a^2})
fit <- sensitivity_analysis(y, X, ipw = 1 / infl$a, ipw_infl = infl$L_ainv,
                            time_wt = (1 - npmle$cdf[match_indx, 2]) * infl$a, 
                            time_wt_infl = (-infl$L_F[match_indx, ] * infl$a) + 
                              (1 - npmle$cdf[match_indx, 2]) * infl_a_est,
                            trunc_mass = seq(0, 0.2, by = 0.02), beta_init = c(1,0))
fit$ci1 <- cbind(fit$coef[, 1] - qnorm(0.975)*fit$se[, 1], fit$coef[, 1] + qnorm(0.975)*fit$se[, 1])
fit$si1 <- cbind(cummin(fit$ci1[, 1]), cummax(fit$ci1[, 2]))
fit$ci2 <- cbind(fit$coef[, 2] - qnorm(0.975)*fit$se[, 2], fit$coef[, 2] + qnorm(0.975)*fit$se[, 2])
fit$si2 <- cbind(cummin(fit$ci2[, 1]), cummax(fit$ci2[, 2]))
sens_results <- data.frame(trunc_mass = fit$trunc_mass,
                           `coef (age <=4)` = fit$coef[, 1],
                           `lower_si (age <=4)` = fit$si1[, 1],
                           `upper_si (age <=4)` = fit$si1[, 2],
                           `coef (age 4-59)` = fit$coef[, 2],
                           `lower_si (age 4-59)` = fit$si2[, 1],
                           `upper_si (age 4-59)` = fit$si2[, 2], check.names = FALSE)
sens_results