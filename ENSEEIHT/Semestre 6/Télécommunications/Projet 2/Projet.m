clear all;
close all;

Fe = 24000;
Rb = 6000;
Tb = 1/Rb;
Rs = Rb;
%Implantation de la chaine sans erreur de phase et sans bruit
%Ns = Ts/Te = Fe/Rs avec Rb=Rs et Ts=1/Rs
%Ns = 24000/3000;
Ns = Fe/Rs;

%% Génération de l'information binaire
n = 1000;
bits = randi([0,1],1,n);

%% ------------------------------------------------------------ %%
%% Implantation de la chaine sans erreur de phase et sans bruit
%% ------------------------------------------------------------ %%
figure('Name', " Implantation de la chaine sans erreur de phase et sans bruit");
%% Mapping 
symboles = 2 * bits - 1;

%% Echantillonage
a = kron(symboles, [1 zeros(1,Ns -1)]);

%% Filtrage de mise en forme
h = ones(1,Ns);
x = filter(h,1,a);

%% Signal en sortie du filtre de mise en forme
subplot(2,3,1);
plot(x);
xlabel("temps");
ylabel("x(t)");
title("Signal en sortie du filtre de mise en forme");

%% Filtrage de récéption
hr = fliplr(h);
x_sortie = filter(hr,1,x);

%% Signal en sortie du filtre de réception
subplot(2,3,2);
plot(x_sortie);
xlabel("temps");
ylabel("x(t)");
title("Signal en sortie du filtre de réception");

%% Réponse impulsionnelle de la chaine de transmission
g = conv(h, hr);

subplot(2,3,3);
plot(g);
xlabel("temps");
ylabel("g");
title("Réponse impulsionnelle de la chaine de transmission");

%% Diagramme de l'oeil
subplot(2,3,4);
plot(reshape(x_sortie,Ns ,length(x_sortie)/Ns ));
title("Diagramme de l'oeil");

%% Echantillonage
n0 = 4;
x_m = x_sortie(n0:Ns:end);

%% Signal en sortie de l'échantillonneur
subplot(2,3,5);
plot(x_m);
xlabel("temps");
ylabel("x_m(t)");
title("Signal en sortie de l'échantillonneur");
%% 1 !!!!
%% Constellations
constellation = (x_m>=0)*1 + (x_m<0)*(-1);
subplot(2,3,6);
plot(constellation, zeros(1,length(constellation)),'o');
xlim([-4 4]);
ylim([-4 4]);
title("Constellations (sans erreur | sans bruit)");
grid on;

%% Demapping 
bits_recus = real(x_m)>0;

%% TEB
erreurs=sum(bits ~= bits_recus);
TEB=erreurs/n;
disp(['Pour une chaine sans erreur de phase et sans bruit : TEB = ', num2str(TEB)]);

%% ------------------------------------------------------------ %%
%% Implantation de la chaine avec erreur de phase et sans bruit
%% ------------------------------------------------------------ %%
figure('Name', " Implantation de la chaine avec erreur de phase et sans bruit");

%% Signal en sortie du filtre de mise en forme
subplot(2,3,1);
plot(x);
xlabel("temps");
ylabel("x(t)");
title("Signal en sortie du filtre de mise en forme (phi=40)");

%% Ajout de l'erreur de phase
% phi = 40
phi_ang = 40;
phi_40 = (phi_ang/180)*pi;
x_dephasage_40 = x * exp(1j*phi_40);
% phi = 100
phi_ang = 100;
phi_100 = (phi_ang/180)*pi;
x_dephasage_100 = x * exp(1j*phi_100);
% phi = 180
phi_ang = 180;
phi_180 = (phi_ang/180)*pi;
x_dephasage_180 = x * exp(1j*phi_180);

%% Filtrage de réception
% phi = 40
x_sortie_40 = filter(hr,1,x_dephasage_40);
% phi = 100
x_sortie_100 = filter(hr,1,x_dephasage_100);
% phi = 180
x_sortie_180 = filter(hr,1,x_dephasage_180);

%% Signal en sortie du filtre de réception
subplot(2,3,2);
plot(x_sortie_40);
xlabel("temps");
ylabel("x(t)");
title("Signal en sortie du filtre de réception (phi=40)");

%% Réponse impulsionnelle de la chaine de transmission
g = conv(h, hr);

subplot(2,3,3);
plot(g);
xlabel("temps");
ylabel("g");
title("Réponse impulsionnelle de la chaine de transmission (phi=40)");

%% Echantillonage
n0 = 4;
% phi =40
x_m_40 = x_sortie_40(n0:Ns:end);
% phi = 100
x_m_100 = x_sortie_100(n0:Ns:end);
% phi = 180
x_m_180 = x_sortie_180(n0:Ns:end);

%% Diagramme de l'oeil
subplot(2,3,4);
plot(reshape(x_sortie_40,Ns ,length(x_sortie)/Ns ));
title("Diagramme de l'oeil (phi=40)");

%% Signal en sortie de l'échantillonneur
subplot(2,3,5);
plot(x_m_40);
xlabel("temps");
ylabel("x_m(t)");
title("Signal en sortie de l'échantillonneur");

%% Constellations
subplot(2,3,6);
plot(x_m_40,'o');
xlim([-4 4]);
ylim([-4 4]);
title("Constellations (avec erreur | sans bruit) phi =40");
grid on;

%% Constellations phi = 40, 100, 180
figure('Name', "Constellation (avec erreur | sans bruit)");

subplot(1,3,1);
plot(x_m_40,'o');
xlim([-4 4]);
ylim([-4 4]);
title("Constellations (avec erreur | sans bruit) phi =40");
grid on;

subplot(1,3,2);
plot(x_m_100,'o');
xlim([-4 4]);
ylim([-4 4]);
title("Constellations (avec erreur | sans bruit) phi =100");
grid on;

subplot(1,3,3);
plot(x_m_180,'o');
xlim([-4 4]);
ylim([-4 4]);
title("Constellations (avec erreur | sans bruit) phi =180");
grid on;

%% Demapping
% phi = 40
bits_recus_40 = real(x_m_40)>0;
% phi = 100
bits_recus_100 = real(x_m_100)>0;
% phi = 180
bits_recus_180 = real(x_m_180)>0;

%% TEB
% phi = 40
erreurs_40=sum(bits ~= bits_recus_40);
% phi = 100
erreurs_100=sum(bits ~= bits_recus_100);
% phi = 180
erreurs_180=sum(bits ~= bits_recus_180);

TEB_40=erreurs_40/n;
disp(['Pour une chaine avec erreur de phase (phi=40) et sans bruit : TEB = ', num2str(TEB_40)]);
TEB_100=erreurs_100/n;
disp(['Pour une chaine avec erreur de phase (phi=100) et sans bruit : TEB = ', num2str(TEB_100)]);
TEB_180=erreurs_180/n;
disp(['Pour une chaine avec erreur de phase (phi=180) et sans bruit : TEB = ', num2str(TEB_180)]);

%% ------------------------------------------------------------ %%
%% Implantation de la chaine avec erreur de phase et avec bruit
%% ------------------------------------------------------------ %%
figure('Name', " Implantation de la chaine avec erreur de phase et avec bruit");

%% Signal en sortie du filtre de mise en forme
subplot(1,3,1);
plot(x);
xlabel("temps");
ylabel("x(t)");
title("Signal en sortie du filtre de mise en forme");

%% Ajout du buit pour EbN0dB = 11
eb_n0 = 11;
M = 2;
P_x = mean(abs(x).^2);
sigma_n = sqrt(P_x * Ns /(2*log2(M)*eb_n0));
bruit = sigma_n' * randn(1,length(x)) + j*sigma_n' * randn(1,length(x));
x_bruite = x + bruit;

%% Ajout de l'erreur de phase en rad
phi_ang = 40;
phi = (phi_ang/180)*pi;
x_dephasage_bruite = x_bruite * exp(1j*phi);

%% Fitrage de réception
x_sortie_bruite = filter(hr,1,x_dephasage_bruite);

%% Signal en sortie du filtre de réception
subplot(1,3,2);
plot(x_sortie_bruite);
xlabel("temps");
ylabel("x(t)");
title("Signal en sortie du filtre de réception");

%% Echantillonage
n0 = 4;
x_m_bruite = x_sortie_bruite(n0:Ns:end);

%% Constellations
subplot(1,3,3);
plot(x_m_bruite,'o');
xlim([-4 4]);
ylim([-4 4]);
title("Constellations");
grid on;

%% Demapping
bits_recus_bruite = real(x_m_bruite)>0;

%% TEB
erreurs_bruite=sum(bits ~= bits_recus_bruite);
TEB_bruite=erreurs_bruite/n;
disp(['Pour une chaine avec erreur de phase (phi=40) et avec bruit : TEB = ', num2str(TEB)]);


%% ------------------------------------------------------------ %%
EbN0dB = [0:6];
EbN0 = 10.^(EbN0dB/10);
%% ------------------------------------------------------------ %%

%% ------------------------------------------------------------ %%
%% Implantation de la chaine avec erreur de phase et avec bruit
%% ------------------------------------------------------------ %%

%% ------------------------- phi = 40 ------------------------- %%
TEB_Simule_40 = zeros(1, 7);
%% -------------------------- phi = 0 ------------------------- %%
TEB_Simule_0 = zeros(1, 7);
%% ------------------------ phi = 100 ------------------------- %%
TEB_Simule_100 = zeros(1, 7);

for i=1:7

    %% Ajout du bruit
    sigma_n = sqrt(P_x * Ns /(2*log2(M)*EbN0(i)));
    bruit = sigma_n' * randn(1,length(x)) + 1j*sigma_n' * randn(1,length(x));
    x_bruite = x + bruit;

    %% Ajout de l'erreur de phase
    % phi = 40
    phi_ang = 40;
    phi_40 = (phi_ang/180)*pi;
    x_dephasage_bruite_40 = x_bruite * exp(1j*phi_40);
    % phi = 0
    phi_ang = 0;
    phi_0 = (phi_ang/180)*pi;
    x_dephasage_bruite_0 = x_bruite * exp(1j*phi_0);
    % phi = 100
    phi_ang = 100;
    phi_100 = (phi_ang/180)*pi;
    x_dephasage_bruite_100 = x_bruite * exp(1j*phi_100);

    %% Filtrage de réception
    % phi = 40
    x_sortie_bruite_40 = filter(hr,1,x_dephasage_bruite_40);
    % phi = 0
    x_sortie_bruite_0 = filter(hr,1,x_dephasage_bruite_0);
    % phi = 100
    x_sortie_bruite_100 = filter(hr,1,x_dephasage_bruite_100);
    
    %% Echantillonage
    n0 = 4;
    % phi =40
    x_m_bruite_40 = x_sortie_bruite_40(n0:Ns:end);
    % phi = 0
    x_m_bruite_0 = x_sortie_bruite_0(n0:Ns:end);
    % phi = 100
    x_m_bruite_100 = x_sortie_bruite_100(n0:Ns:end);

    %% Demapping
    % phi = 40
    bits_recus_bruite_40 = real(x_m_bruite_40)>0;
    % phi = 0
    bits_recus_bruite_0 = real(x_m_bruite_0)>0;
    % phi = 100
    bits_recus_bruite_100 = real(x_m_bruite_100)>0;

    %% TEB
    % phi = 40
    erreurs_bruite_40=sum(bits ~= bits_recus_bruite_40);
    TEB_Simule_40(i) = erreurs_bruite_40/n;
    % phi = 0
    erreurs_bruite_0=sum(bits ~= bits_recus_bruite_0);
    TEB_Simule_0(i) = erreurs_bruite_0/n;
    % phi = 100
    erreurs_bruite_100=sum(bits ~= bits_recus_bruite_100);
    TEB_Simule_100(i) = erreurs_bruite_100/n;
end
%% TEB Théorique
TEB_Theorique = cos(phi_40) * qfunc(sqrt(EbN0));

%% Comparaison de TEB Simulé et Théorique pour phi=40
figure('Name', "Comparaison de TEB Simulé et Théorique pour phi=40");
semilogy(EbN0dB, TEB_Simule_40);
title("Comparaison de TEB Simulé et Théorique pour phi=40");
hold on;
semilogy(EbN0dB, TEB_Theorique);
legend('TEB Simule', 'TEB Théorique');
hold off;

%% Comparaison de TEB Simulé (phi=40) et TEB Simulé (phi=0)
figure('Name', "Comparaison de TEB Simulé (phi=40) et TEB Simulé (phi=0)");
semilogy(EbN0dB, TEB_Simule_40);
title("Comparaison de TEB Simulé (phi=40) et TEB Simulé (phi=0)");
hold on;
semilogy(EbN0dB, TEB_Simule_0);
legend('TEB Simulé (phi=40)', 'TEB Simulé (phi=0)');
hold off;

%% Comparaison de TEB Simulé (phi=40) et TEB Simulé (phi=100)
figure('Name', "Comparaison de TEB Simulé (phi=40) et TEB Simulé (phi=100)");
semilogy(EbN0dB, TEB_Simule_40);
title("Comparaison de TEB Simulé (phi=40) et TEB Simulé (phi=100)");
hold on;
semilogy(EbN0dB, TEB_Simule_100);
legend('TEB Simulé (phi=40)', 'TEB Simulé (phi=100)');
hold off;

%% ------------------------------------------------------------ %%
%% Implantation de la chaine avec erreur de phase et avec bruit
%% ---------- sans correction et avec correction -------------- %%
%% ------------------------------------------------------------ %%

%% Ajout du buit pour EbN0dB = 11
eb_n0 = 11;

%% Ajout du bruit
sigma_n = sqrt(P_x * Ns /(2*log2(M)*eb_n0));
bruit = sigma_n' * randn(1,length(x)) + 1j*sigma_n' * randn(1,length(x));
x_bruite = x + bruit;

%% Ajout de l'erreur de phase
% phi = 40
phi_ang = 40;
phi_40 = (phi_ang/180)*pi;
x_dephasage_bruite_40 = x_bruite * exp(1j*phi_40);
% phi = 100
phi_ang = 100;
phi_100 = (phi_ang/180)*pi;
x_dephasage_bruite_100 = x_bruite * exp(1j*phi_100);

%% Filtrage de réception
% phi = 40
x_sortie_bruite_40 = filter(hr,1,x_dephasage_bruite_40);
% phi = 100
x_sortie_bruite_100 = filter(hr,1,x_dephasage_bruite_100);

%% Echantillonage
n0 = 4;
% phi =40
x_m_bruite_40 = x_sortie_bruite_40(n0:Ns:end);
% phi = 100
x_m_bruite_100 = x_sortie_bruite_100(n0:Ns:end);

%% Calcul de phi chapeau 
% phi =40
arg_phi_40 = 0.5*sum(x_m_bruite_40 .* x_m_bruite_40);
phi_rad_40 = angle(arg_phi_40);
% phi =100
arg_phi_100 = 0.5*sum(x_m_bruite_100 .* x_m_bruite_100);
phi_rad_100 = angle(arg_phi_100);

%% Correction
x_m_corrige_40 = x_m_bruite_40 * exp(-1j * phi_rad_40);
x_m_corrige_100 = x_m_bruite_100 * exp(-1j * phi_rad_100);

%% Demapping sans correction
% phi = 40
bits_recus_bruite_40 = real(x_m_bruite_40)>0;
% phi = 100
bits_recus_bruite_100 = real(x_m_bruite_100)>0;

%% Demapping avec correction
% phi = 40
bits_recus_bruite_40_corrige = real(x_m_corrige_40)>0;
% phi = 100
bits_recus_bruite_100_corrige = real(x_m_corrige_100)>0;

%% TEB sans correction
% phi = 40
erreurs_bruite_40=sum(bits ~= bits_recus_bruite_40);
TEB_Simule_sans_correction = erreurs_bruite_40/n;
% phi = 100
erreurs_bruite_100=sum(bits ~= bits_recus_bruite_100);
TEB_100_sans_correction = erreurs_bruite_100/n;

%% TEB avec correction
% phi = 40
erreurs_bruite_40_corrige=sum(bits ~= bits_recus_bruite_40_corrige);
TEB_40_avec_correction = erreurs_bruite_40_corrige/n;
disp(['Pour une chaine avec erreur de phase (phi=40) et avec bruit AVEC CORRECTION: TEB = ', num2str(TEB_40_avec_correction)]);

% phi = 100
erreurs_bruite_100_corrige=sum(bits ~= bits_recus_bruite_100_corrige);
TEB_100_avec_correction = erreurs_bruite_100_corrige/n;
disp(['Pour une chaine avec erreur de phase (phi=100) et avec bruit AVEC CORRECTION: TEB = ', num2str(TEB_100_avec_correction)]);


%% ------------------------------------------------------------ %%
%% Implantation de la chaine avec erreur de phase et avec bruit
%% ---------- sans correction et avec correction -------------- %%
%% ------------------------------------------------------------ %%

%% ------------------------- phi = 40 ------------------------- %%
TEB_Simule_40 = zeros(1, 7);
TEB_Simule_40_corrige = zeros(1, 7);

%% ------------------------ phi = 100 ------------------------- %%
TEB_Simule_100 = zeros(1, 7);
TEB_Simule_100_corrige = zeros(1, 7);

for i=1:7

    %% Ajout du bruit
    sigma_n = sqrt(P_x * Ns /(2*log2(M)*EbN0(i)));
    bruit = sigma_n' * randn(1,length(x)) + 1j*sigma_n' * randn(1,length(x));
    x_bruite = x + bruit;

    %% Ajout de l'erreur de phase
    % phi = 40
    phi_ang = 40;
    phi_40 = (phi_ang/180)*pi;
    x_dephasage_bruite_40 = x_bruite * exp(1j*phi_40);
    % phi = 100
    phi_ang = 100;
    phi_100 = (phi_ang/180)*pi;
    x_dephasage_bruite_100 = x_bruite * exp(1j*phi_100);

    %% Filtrage de réception
    % phi = 40
    x_sortie_bruite_40 = filter(hr,1,x_dephasage_bruite_40);
    % phi = 100
    x_sortie_bruite_100 = filter(hr,1,x_dephasage_bruite_100);
    
    %% Echantillonage
    n0 = 4;
    % phi =40
    x_m_bruite_40 = x_sortie_bruite_40(n0:Ns:end);
    % phi = 100
    x_m_bruite_100 = x_sortie_bruite_100(n0:Ns:end);
    
    %% Calcul de phi chapeau 
    % phi =40
    arg_phi_40 = 0.5*sum(x_m_bruite_40 .* x_m_bruite_40);
    phi_rad_40 = angle(arg_phi_40);
    % phi =100
    arg_phi_100 = 0.5*sum(x_m_bruite_100 .* x_m_bruite_100);
    phi_rad_100 = angle(arg_phi_100);
    
    %% Correction
    x_m_corrige_40 = x_m_bruite_40 * exp(-1j * phi_rad_40);
    x_m_corrige_100 = x_m_bruite_100 * exp(-1j * phi_rad_100);

    %% Demapping sans correction
    % phi = 40
    bits_recus_bruite_40 = real(x_m_bruite_40)>0;
    % phi = 100
    bits_recus_bruite_100 = real(x_m_bruite_100)>0;

    %% Demapping avec correction
    % phi = 40
    bits_recus_bruite_40_corrige = real(x_m_corrige_40)>0;
    % phi = 100
    bits_recus_bruite_100_corrige = real(x_m_corrige_100)>0;

    %% TEB sans correction
    % phi = 40
    erreurs_bruite_40=sum(bits ~= bits_recus_bruite_40);
    TEB_Simule_40(i) = erreurs_bruite_40/n;
    % phi = 100
    erreurs_bruite_100=sum(bits ~= bits_recus_bruite_100);
    TEB_Simule_100(i) = erreurs_bruite_100/n;

    %% TEB avec correction
    % phi = 40
    erreurs_bruite_40_corrige=sum(bits ~= bits_recus_bruite_40_corrige);
    TEB_Simule_40_corrige(i) = erreurs_bruite_40_corrige/n;
    % phi = 100
    erreurs_bruite_100_corrige=sum(bits ~= bits_recus_bruite_100_corrige);
    TEB_Simule_100_corrige(i) = erreurs_bruite_100_corrige/n;
end

%% Comparaison du TEB Simulé avec et sans correction (phi=40)
figure('Name',"Comparaison du TEB Simulé avec et sans correction (phi=40)");
semilogy(EbN0dB, TEB_Simule_40);
title("Comparaison du TEB Simulé avec et sans correction (phi=40)");
hold on;
semilogy(EbN0dB, TEB_Simule_40_corrige);
legend('TEB Simulé sans Correction (phi=40)','TEB Simulé avec Correction (phi=40)');
hold off;

%% Comparaison du TEB Simulé avec et sans correction (phi=100)
figure('Name',"Comparaison du TEB Simulé avec et sans correction (phi=100)");
semilogy(EbN0dB, TEB_Simule_100);
title("Comparaison du TEB Simulé avec et sans correction (phi=100)");
hold on;
semilogy(EbN0dB, TEB_Simule_100_corrige);
legend('TEB Simulé sans Correction (phi=100)','TEB Simulé avec Correction (phi=100)');
hold off;
