clear all
close all
%% Utilisation de la chaine passe-bas équivalente pour le calcul et l'estimation du taux d'erreur binaire

%% Implantation de la chaine sur fréquence porteuse

% Transmission QPSK :
M = 4;                                          %ordre

% Nombre de bits générés
n=1000;

% Génération de l'information binaire
bits = randi([0,1], 1, n);

alpha = 0.35;                                   %roll-off
fp = 2000;                                      %(Hz) fréquence porteuse
fe = 10000;                                     %(Hz) fréquence d'échantillonnage
Te = 1/fe;
Rb = 2000;                                      %débit binaire bits/s
Tb = 1/Rb;                                      %période binaire
Rs = Rb/log2(M);                                %débit symbole
Ts = 1/Rs;                                      %période symbole
Ns = Ts*fe;                                     %facteur de suréchantillonnage
%t = [0:Te: Ns*Ts]; 
EbN0dB = [0:6];

%% Mapping
dk=1-2*bits(1:2:n)+j*(1-2*bits(2:2:n));

%% Coonstellation
ak = real(dk);
bk = imag(dk);
figure('Name', "Constellation  QPSK (bk = f(ak))");
plot(ak,bk,'linestyle','none','marker','o');
title( "Constellation  QPSK (bk = f(ak))");

%% Signal suréchantillonné
a = kron(dk, [1 zeros(1,Ns-1)]); 

%% Filtre de cosinus surélevé
span = 5;
sps = Ns;
h = rcosdesign(alpha, span, sps);               %filtre pour la modulation en bande de base avec symboles complexes

%% Filtrage de mise en forme
xe = filter(h,1,[a zeros(1,length(h))]);
t = [0:Te:(length(xe)-1)*Te];

figure('Name', "xe(t) : Enveloppe complexe associée à x(t)");
plot(t,xe);
xlabel('Temps (s)'); 
ylabel('xe(t)');
title('xe(t) : Enveloppe complexe associée à x(t)');

%% Tracé de la densité spectrale de puissance : Sxe(f)

Sxe_f = (1/length(xe))*abs(fft(xe)).^2;
f = linspace(0,fe,length(Sxe_f));
figure('Name', "Sxe(f) : Densité spectrale de puissance de xe");
plot(f,Sxe_f);
xlabel('Fréquence (Hz)') ;
ylabel('Sxe(f)');
title('Sxe(f) : Densité spectrale de puissance de xe');

%% Signaux générés sur les voies en phase et en quadrature 

i = real(xe);                                   % voie en phase (à afficher)
figure('Name', "i(t) : Voie en phase");
plot(t,i);
xlabel('Temps (s)') ;
ylabel('i(t)');
title('i(t) : Voie en phase');
% 
q = imag(xe);                                   % voie en quadrature (à afficher)
figure('Name', "q(t) : Voie en quadrature");
plot(t,q);
xlabel('Temps (s)'); 
ylabel('q(t)');
title('q(t) : Voie en quadrature');

%% X: Signal transmis sur fréquence porteuse.
icos = i.*cos(2*pi*fp*t);
qsin = q.*sin(2*pi*fp*t);
x = icos - qsin;

figure('Name', "x(t) : Signal sur fréquence porteuse");
plot(t,x);
xlabel('Temps (s)') ;
ylabel('x(t)');
title("x(t) : Signal sur fréquence porteuse");

%% Densité spectrale de puissance du signal modulé sur fréquence porteuse. 
Sx_f = (1/length(x)) * abs(fft(x)).^2;
f = linspace(0,fe,length(Sx_f));
figure('Name', 'Sx(f) : Estimation de la densité spectrale');
semilogy(f,Sx_f);
xlabel('Fréquence (Hz)') ;
ylabel('Sx(f)');
title("Sx(f) : Estimation de la densité spectrale");

%% Implantation de la chaine complète sans bruit afin de vérifier que le TEB obtenu est bien nul.

%% Calcul de x retour
xcos = x.*cos(2*pi*fp*t);                       %partie cosinus
xsin = -j*x.*sin(2*pi*fp*t);                    %partie sinus

x_retour = xcos + xsin;                         %signal en sortie du retour en bande de base

figure('Name', "x_retour(t) : Signal en sortie du retour en bande de base");
plot(t,x_retour);
xlabel('Temps (s)') ;
ylabel('x_retour(t)');
title("x_retour(t) : Signal en sortie du retour en bande de base");

%% Fitrage de réception
z = filter(h,1,x_retour);                       %signal en sortie du filtre de réception
figure('Name', "z(t) : Signal en sortie du filtre de réception");
plot(t,z);
xlabel('Temps (s)'); 
ylabel('z(t)');
title("z(t) : Signal en sortie du filtre de réception");

%% Echantillonage
zm=z(length(h)+1:Ns:length(z));                 %signal échantilloné

%% Demapping
bits_recus(1:2:n)=(real(zm)<0);                 %ak
bits_recus(2:2:n)=(imag(zm)<0);                 %bk

%% TEB
TEB = sum(bits~=bits_recus);
if sum(bits~=bits_recus)==0
    display('TEB = 0 ');
end

%% Ajout le bruit tracé du taux d'erreur binaire obtenu en fonction du rapport signal à bruit par bit
%% à l'entrée du récepteur (Eb/N0) en décibels. 

Puissance_recu = mean(abs(x).^2);
TEB_bruite_matrice = zeros(1,7);
TEB_theorique_matrice = zeros(1,7);
for i = 0:6
    EbN0 = 10^(i/10);
    sigma_n = sqrt((Puissance_recu*Ns)/(2*log2(M)*(EbN0)));
    bruit =  sigma_n * randn(1, length(x));

    %% Ajout du bruit
    x_bruite = x + bruit;

    %% X_bruite_retour
    x_bruitecos = x_bruite.*cos(2*pi*fp*t);
    x_bruitesin = -j*x_bruite.*sin(2*pi*fp*t);
    x_bruite_retour = x_bruitecos + x_bruitesin;

    %% Filtrage de réception
    z_bruite = filter(h,1,x_bruite_retour);

    %% Echantillonage
    zm_bruite=z_bruite(length(h)+1:Ns:length(z_bruite));
    
    %% Demapping
    bits_recus_bruite(1:2:n)=(real(zm_bruite)<0); %ak
    bits_recus_bruite(2:2:n)=(imag(zm_bruite)<0); %bk
    
    erreur = sum(bits~=bits_recus_bruite);
    TEB_bruite = erreur/n;
    TEB_bruite_matrice(i+1) = TEB_bruite;
    if sum(bits~=bits_recus_bruite)==0
        display('OK! (bruite) ')
    end

    TEB_theorique = qfunc(sqrt(2*EbN0));
    TEB_theorique_matrice(i+1) = TEB_theorique;
end

%% TEB simulé
figure;
semilogy(EbN0dB,TEB_theorique_matrice,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB ');
grid;


%% Comparaison du TEB simulé au TEB théorique de la chaine étudiée 
figure("Name", 'Comparaison TEB simulée et TEB théorique');
semilogy(EbN0dB,TEB_bruite_matrice);
hold on;
semilogy(EbN0dB,TEB_theorique_matrice);
legend('Simulée', 'Théorique');
xlabel('Eb/No (dB)') ;
ylabel('TEB');
title('Comparaison TEB simulée et TEB théorique');

%% Implantation de la chaine passe-bas ́equivalente

%% Constellation
ak_pbe = real(dk);
bk_pbe = imag(dk);
figure('Name', "Constellation  QPSK (bk = f(ak))");
plot(ak_pbe,bk_pbe,'linestyle','none','marker','o');
xlabel('ak') ;
ylabel('bk');
title("Constellation  QPSK (bk = f(ak))");

%% signal suréchantillonné
a_pbe = kron(dk, [1 zeros(1,Ns-1)]);             %signal suréchantillonné

%% Filtre de cos surélevé
span = 5;
sps = Ns;
h = rcosdesign(alpha, span, sps);                %filtre pour la modulation en bande de base avec symboles complexes

%% Filtrage de mise en forme
xe_pbe = filter(h,1,[a_pbe zeros(1,length(h))]);
t = [0:Te:(length(xe_pbe)-1)*Te];

figure('Name', "xe(t) : Enveloppe complexe associée à x(t)");
plot(t,xe_pbe);
xlabel('Temps (s)') ;
ylabel('xe(t)');
title("xe(t) : Enveloppe complexe associée à x(t)");

i_pbe = real(xe_pbe);                            %voie en phase (à afficher)
figure('Name', "i(t) : Voie en phase (passe-bas équivalent)");
plot(t,i_pbe);
xlabel('Temps (s)') ;
ylabel('i(t) passe-bas équivalent');
title("i(t) : Voie en phase (passe-bas équivalent)");

q_pbe = imag(xe_pbe);                            %voie en quadrature (à afficher)
figure('Name', "q(t) : Voie en quadrature (passe-bas équivalent)");
plot(t,q_pbe);
xlabel('Temps (s)') ;
ylabel('q(t) passe-bas équivalent');
title("q(t) : Voie en quadrature (passe-bas équivalent)");


%% Tracé de la densité spectrale de puissance : Sxe(f)
Sxe_f_pbe = (1/length(xe_pbe))*abs(fft(xe_pbe)).^2;
f = linspace(0,fe,length(Sxe_f_pbe));

figure('Name', "Sxe(f) : Densité spectrale de puissance de xe (passe-bas équivalent)"),
plot(f,Sxe_f_pbe);
xlabel('Fréquence (Hz)') ;
ylabel('Sxe(f) passe-bas équivalent');
title("Sxe(f) : Densité spectrale de puissance de xe (passe-bas équivalent)");

%% Implantation la chaine complète sans bruit afin de vérifier que le TEB obtenu est bien nul.
x_pbe = xe_pbe;

%% Filtrage de réception
z_pbe = filter(h,1,x_pbe);                       %signal en sortie du filtre de réception
figure('Name', "z(t) : Signal en sortie du filtre de réception (passe-bas équivalent)");
plot(t,z_pbe);
xlabel('Temps (s)') 
ylabel('z(t) passe-bas équivalent');
title("z(t) : Signal en sortie du filtre de réception (passe-bas équivalent)");

%% Echantillonage
zm_pbe=z_pbe(length(h)+1:Ns:length(z_pbe));

%% Demapping
bits_recus_pbe(1:2:n)=(real(zm_pbe)<0);          %ak
bits_recus_pbe(2:2:n)=(imag(zm_pbe)<0);          %bk

%% TEB
TEB_pbe = sum(bits~=bits_recus_pbe);
if sum(bits~=bits_recus_pbe)==0
    display('TEB = 0 (passe-bas équivalent)');
end

%% Ajout du bruit et tracé du taux d'erreur binaire obtenu en fonction du rapport signal à bruit par bit
%% à l'entrée du récepteur (Eb/N0) en décibels.
figure('Name', 'Constellations QPSK (bk = f(ak)) (passe-bas équivalent)');
Puissance_recu = mean(abs(x_pbe).^2);
TEB_bruite_matrice_pbe = zeros(1,7);
TEB_theorique_matrice_pbe = zeros(1,7);
for i = 0:6
    EbN0 = 10^(i/10);
    sigma_n_pbe = sqrt((Puissance_recu*Ns)/(2*log2(M)*(EbN0)));
    bruit_pbe =  sigma_n_pbe * randn(1, length(x_pbe)) + j*sigma_n_pbe * randn(1, length(x_pbe));
    
    %% Ajout du bruit
    x_bruite_pbe = x_pbe + bruit_pbe;

    %% Filtrage de réception
    z_bruite_pbe = filter(h,1,x_bruite_pbe);

    %% Echantillonage
    zm_bruite_pbe=z_bruite_pbe(length(h)+1:Ns:length(z_bruite_pbe));
    
    %% Demapping
    bits_recus_bruite_pbe(1:2:n)=(real(zm_bruite_pbe)<0); %ak
    bits_recus_bruite_pbe(2:2:n)=(imag(zm_bruite_pbe)<0); %bk

    %% Tracé des constellations en sortie du mapping et en sortie de l'échantillonneur pour différentes valeurs
    %% de Eb/N0. Expliquez les différences observées.
    ak_pbe = (real(zm_bruite_pbe));
    bk_pbe = (imag(zm_bruite_pbe));
    if i<6
        pos = i+1;
    else
        pos =8;
    end
    subplot(3,3,pos);

    plot(ak_pbe,bk_pbe,'linestyle','none','marker','o');
    xlabel('ak passe-bas équivalent') ;
    ylabel('bk passe-bas équivalent');
    title('EbN0dB = ' , num2str( i));

    erreur_pbe = sum(bits~=bits_recus_bruite_pbe);
    TEB_bruite_pbe = erreur_pbe/n;
    TEB_bruite_matrice_pbe(i+1) = TEB_bruite_pbe;
    if sum(bits~=bits_recus_bruite_pbe)==0
        display('You''re awesome bruite pbe ! ! ! ')
    end
    TEB_theorique_pbe = qfunc(sqrt(2*EbN0));
    TEB_theorique_matrice_pbe(i+1) = TEB_theorique_pbe;
end

%% TEB simulé
figure;
semilogy(EbN0dB,TEB_bruite_matrice_pbe,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB ');
grid;


%% Comparaison
figure("Name", 'Comparaison TEB simulée et TEB théorique (passe-bas équivalent)');
semilogy(EbN0dB,TEB_bruite_matrice_pbe);
hold on;
semilogy(EbN0dB,TEB_theorique_matrice_pbe);
legend('Simulée passe-bas équivalent', 'Théorique passe-bas équivalent');
xlabel('Eb/No (dB)') ;
ylabel('TEB');
title('Comparaison TEB simulée et TEB théorique (passe-bas équivalent)');

%% Vérifiez que l'on obtient bien le même TEB que celui obtenu avec la chaine simulée sur fréquence
%% porteuse (tracé sur une même figure).
figure("Name", 'Comparaison des TEB pour les deux chaines');
semilogy(EbN0dB,TEB_bruite_matrice_pbe);
hold on;
semilogy(EbN0dB,TEB_bruite_matrice);
legend('Chaine PBE', 'Chaine sur fréquence porteuse');
xlabel('Eb/No (dB)') ;
ylabel('TEB');
title('Comparaison des TEB pour les deux chaines');

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%