clear all
close all
%% ------------------------ 4-ASK -------------------------- %%

%% Génération de l'information binaire
M = 4;
n=1000;
bits = randi([0,1], 1, n);

fp = 2000; %Hz fréquence porteuse
fe = 240000; %Hz fréquence d'échantillonnage
Rb = 48000;%48000
TEB_th = 10^(-2);
Te = 1/fe;
Tb = 1/Rb; %période binaire
Rs = Rb/log2(M); %débit symbole
Ts = 1/Rs; %période symbole
Ns = Ts*fe; %facteur de suréchantillonnage
EbN0dB = [0:6];

%% Filtre de cosinus surélevé
alpha = 0.5;
span = 8;
sps = Ns;
h = rcosdesign(alpha, span, sps);

%% Mapping Symboles 4-aires à moyenne nulle 
% Symboles1 = reshape(bits, n/2, 2);
% Symboles2 = bi2de(Symboles1);
% Symboles = (2 * Symboles2 -3)'; %dk
Symboles = (2 * bi2de(reshape(bits, 2, length(bits)/2).') - 3).';

%% Constellation 
ak=[-3,-1,1,3];
bk =[0,0,0,0];
figure('Name', "Constellation  4-ASK (bk = f(ak)) après mapping");
plot(ak,bk,'linestyle','none','marker','o');
title( "Constellation  4-ASK (bk = f(ak)) après mapping");

%% Génération de la suite de Diracs pondérés par les symbols (suréchantillonnage)
Suite_diracs = kron(Symboles, [1 zeros(1,Ns-1)]);

%% Filtrage de mise en forme
x=filter(h,1,[Suite_diracs zeros(1,length(h))]);

%% DSP
[DSP,f] = pwelch(x,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (4-ASK) sans bruit");

%% Filtrage de réception
hr = fliplr(h);
z = filter(hr ,1,x);

%% Echantillonnage 
zm=z(length(hr)+1:Ns:length(z));

%% Démapping
x_demap = (0<=zm & zm <2)*1 + (2<zm & zm<4)*3 + (0> zm & zm>-2)*(-1) + (-2>zm & zm>-4)*(-3);
x_demap_transpose = x_demap';
x_demap_2 = (x_demap_transpose+3)/2;
x_retour = de2bi(x_demap_2);
bits_recus = reshape(x_retour,1,n);

%% TEB
taux = sum(bits ~= bits_recus);
TEB = 100 * taux / n;
if taux==0
   disp('TEB = 0 (sans bruit) ');
end
%% ------------------------------------------------------- %%

%% -------------------- Ajout du bruit ------------------- %%
%% Constellation
figure('Name', "Constellation  4-ASK (bk = f(ak)) en sortie de l'échantillonage");

Puissance_recu = mean(abs(x).^2);
TEB_bruite_matrice = zeros(1,7);
TEB_theorique_matrice = zeros(1,7);
for i = 0:6
    EbN0 = 10^(i/10);
    sigma_n = sqrt((Puissance_recu*Ns)/(2*log2(M)*(EbN0)));
    bruit = sigma_n * randn(1, length(x)) + j*sigma_n * randn(1, length(x));
    x_bruite = x + bruit;

    %% Filtre de réception
    z_bruite = filter(h,1,x_bruite);

    %% Echantillonage
    zm=z_bruite(length(h)+1:Ns:length(z_bruite));

    %% Constellation
    if i<6
        pos = i+1;
    else
        pos =8;
    end
    ak =real(zm);
    bk= imag(zm);
    subplot(3,3,pos);
    plot(ak,bk,'linestyle','none','marker','o');
    title('EbN0dB = ' , num2str(i));

    zm_real = real(zm);

    %% Démapping
%     tmp = (zm_real + 3*Ns)/(2*Ns);
%     tmp1 = (tmp <0.5)*0 + (0.5<=tmp & tmp<1.5)*1 + (1.5<=tmp & tmp<2.5)*2 + (2.5<=tmp)*3;
%     bits_recus_bruite = reshape(de2bi(tmp1).', 1, length(bits));

%     x_demap = (0<=zm_real & zm_real <1.75)*1 + (1.75<=zm_real & zm_real<=8)*3 + (0> zm_real & zm_real>-1.75)*(-1) + (-1.75>=zm_real & zm_real>=-8)*(-3);
%     x_demap_transpose = x_demap';
%     x_demap_2 = (x_demap_transpose+3)/2;
%     x_retour = de2bi(x_demap_2);
%     tmp = [x_retour(:,2) x_retour(:,1)];
%     bits_recus_bruite = [];
%     for k=1:length(x_retour(:,1))
%         bits_recus_bruite = [bits_recus_bruite tmp(k,:)];
%     end

    symboles = (-2 * (zm_real <= -2) + sign(zm_real) + 2*(zm_real >= 2) + 3)/2;

    z_demap= de2bi(symboles)';
    bits_recus_bruite = zeros(1,length(bits));
    bits_recus_bruite = z_demap(:)';

    %% TEB
    erreur = sum(bits~=bits_recus_bruite);
    TEB_bruite =erreur/n;
    TEB_bruite_matrice(i+1) = TEB_bruite;
    if sum(bits~=bits_recus_bruite)==0
        disp('TEB = 0 (avec bruit) ');
    end
end
%% ------------------------------------------------------- %%

%% DSP
[DSP,f] = pwelch(x_bruite,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (4-ASK) avec bruit");

%% TEB simulé
figure;
semilogy(EbN0dB,TEB_bruite_matrice,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB ');
grid;


%% Comparaison du TEB simulé au TEB théorique de la chaine étudiée 
TEB_theorique_matrice = qfunc(sqrt(6*log2(M).*(10.^(EbN0dB/10))./(M^2-1)));

figure("Name", 'Comparaison TEB simulée et TEB théorique');
semilogy(EbN0dB,TEB_bruite_matrice,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB,TEB_theorique_matrice);
legend('Simulée', 'Théorique');
xlabel('Eb/No (dB)') ;
ylabel('TEB');
title('Comparaison TEB simulée et TEB théorique');

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%