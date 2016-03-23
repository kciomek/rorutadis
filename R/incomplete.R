

extendModelWithAssignmentComparisonVariables <- function(model, firstAssignmentVariableIndex) {
  numberOfAlternatives <- nrow(model$perfToModelVariables)
  numberOfClasses <- model$nrClasses
  
  firstBinaryVariableIndex <- ncol(model$constraints$lhs) + 1
  
  model$constraints <- addVarialbesToModel(model$constraints, rep("B", numberOfAlternatives * (numberOfAlternatives - 1)))
  nrVariables <- ncol(model$constraints$lhs)
  
  N <- 2 * numberOfClasses
  
  for (i in seq_len(numberOfAlternatives)) {
    for (j in seq_len(numberOfAlternatives)) {
      if (i != j) {
        # c(a_i) - c(a_j) >= 0.5 - N (1 - v_ij) # LB
        # c(a_i) - c(a_j) <= 0.5 + N v_ij # UB
        
        lhsLB <- rep(0, nrVariables)
        lhsUB <- rep(0, nrVariables)
        
        for (h in seq_len(numberOfClasses)) {
          lhsLB[firstAssignmentVariableIndex + (i - 1) * numberOfClasses + h - 1] <- h
          lhsLB[firstAssignmentVariableIndex + (j - 1) * numberOfClasses + h - 1] <- -h
          lhsUB[firstAssignmentVariableIndex + (i - 1) * numberOfClasses + h - 1] <- h
          lhsUB[firstAssignmentVariableIndex + (j - 1) * numberOfClasses + h - 1] <- -h
        }
        
        k <- j
        if (j > i) {
          k <- k - 1
        }
        
        lhsLB[firstBinaryVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] <- -N
        lhsUB[firstBinaryVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] <- -N
        
        model$constraints <- combineConstraints(model$constraints, list(lhs = lhsLB, dir = ">=", rhs = 0.5 - N))
        model$constraints <- combineConstraints(model$constraints, list(lhs = lhsUB, dir = "<=", rhs = 0.5))
      }
    }
  }
  
  return (model)
}


findSolutionWithIncomplete <- function(problem, stochasticResults, method, reg = 1e-20) {
  if (!checkConsistency(problem)) {
    stop("Model infeasible.")
  }
  
  model <- buildModel(problem, FALSE)
  
  if (!("B" %in% model$constraints$types)) { # TODO: replace with some better checking
    model <- extendModelWithAssignmentVariables(model)
  }
  
  firstAssignmentVariableIndex <- model$firstThresholdIndex + model$nrClasses - 1

  if (method %in% c("apoi-product", "combined-product")) {
    model <- extendModelWithAssignmentComparisonVariables(model, firstAssignmentVariableIndex)
  }
  
  objective <- rep(0, ncol(model$constraints$lhs))
  
  numberOfAlternatives <- nrow(problem$perf)
  numberOfClasses <- problem$nrClasses
  
  if (method %in% c("cai-product", "combined-product")) {
    for (i in seq_len(numberOfAlternatives)) {
      for (h in seq_len(numberOfClasses)) {
        objective[firstAssignmentVariableIndex + (i - 1) * numberOfClasses + h - 1] <- log(stochasticResults$assignments[i, h] + reg)
      }
    }
  }
  
  if (method %in% c("apoi-product", "combined-product")) {
    firstAssignmentVariableIndex <- firstAssignmentVariableIndex + numberOfClasses * numberOfAlternatives
    
    for (i in seq_len(numberOfAlternatives)) {
      for (j in seq_len(numberOfAlternatives)) {
        if (i != j) {
          k <- j
          if (j > i) {
            k <- k - 1
          }
          
          objective[firstAssignmentVariableIndex + (i - 1) * (numberOfAlternatives - 1) + k - 1] <- log(stochasticResults$preferenceRelation[i, j] + reg)
        }
      }
    }
  }
  
  solution <- Rglpk_solve_LP(objective, model$constraints$lhs, model$constraints$dir, model$constraints$rhs, max = TRUE,
                        types = model$constraints$types)
  
  return (toSolution(model, solution$solution))
}




