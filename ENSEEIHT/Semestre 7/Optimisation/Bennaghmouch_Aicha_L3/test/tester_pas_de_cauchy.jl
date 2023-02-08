
function tester_pas_de_cauchy(afficher::Bool, Pas_De_Cauchy::Function)
    @testset "Pas de Cauchy" begin
        @testset "Cas test 1 : g = 0" begin
            g = [0; 0]
            H = [7 0; 0 2]
            delta = 1
            s, e = Pas_De_Cauchy(g, H, delta)
            @test (e == 0) && (isapprox(s, [0; 0], atol=tol_erreur))
        end

        @testset "Cas test 2 : Boule saturé avec g = [6; 2]" begin
            g = [6; 2]
            H = [7 0; 0 2]
            delta = 1
            s, e = Pas_De_Cauchy(g, H, delta)
            solution = -(norm(g)^2 / (g' * H * g)) * g
            @test (e == 1) && (isapprox(s, solution, atol=tol_erreur))
        end

        @testset "Cas test 3 : Boule non saturé avec g = [6; 2]" begin
            g = [6; 2]
            H = [7 0; 0 2]
            delta = 0.9
            s, e = Pas_De_Cauchy(g, H, delta)
            solution = -(delta / norm(g)) * g
            @test (e == -1) && (isapprox(s, solution, atol=tol_erreur))
        end

        @testset "Cas test 4 : Boule saturé avec g = [-2; 1]" begin
            g = [-2; 1]
            H = [-2 0; 0 10]
            delta = 6
            s, e = Pas_De_Cauchy(g, H, delta)
            solution = -(norm(g)^2 / (g' * H * g)) * g
            @test (e == 1) && (isapprox(s, solution, atol=tol_erreur))
        end

        @testset "Cas test 5 : Boule non saturé avec g = [-2; 1]" begin
            g = [-2; 1]
            H = [-2 0; 0 10]
            delta = 5
            s, e = Pas_De_Cauchy(g, H, delta)
            solution = -(delta / norm(g)) * g
            @test (e == -1) && (isapprox(s, solution, atol=tol_erreur))
        end

        @testset "quad 3, g'*H*g <0 saturé" begin
            g = [3; 1]
            H = [-2 0; 0 10]
            delta = 5
            s, e = Pas_De_Cauchy(g, H, delta)
            sol = -(delta / norm(g)) * g
            println("Cauchy 6= ", sol)
            @test (e == -1) && (isapprox(s, sol, atol=tol_erreur))
        end

        @testset "quad 3, g'*H*g = 0 saturé" begin
            g = [1, 2]
            H = [2 -1; 4 -2]
            delta = 5
            s, e = Pas_De_Cauchy(g, H, delta)
            solution = -(delta / norm(g)) * g
            @test (e == -1) && (isapprox(s, solution, atol=tol_erreur)) 
        end
    end
end